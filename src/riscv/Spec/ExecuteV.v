(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import Coq.ZArith.BinInt.
Require Import coqutil.Datatypes.ZList.
Local Open Scope Z_scope.

Notation VRegister := BinInt.Z (only parsing).

(* Converted imports: *)

Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Import Coq.ZArith.BinInt.
Require Import Monads.
Require Spec.CSRField.
Require Spec.Decode.
Require Spec.Machine.
Require Spec.VirtualMemory.
Require Import Utility.
Require Utility.Utility.
Require Z.

(* No type declarations to convert. *)

(* Converted value declarations: *)

(* Skipping definition `Spec.ExecuteV.take_machineInt' *)

(* Skipping definition `Spec.ExecuteV.drop_machineInt' *)

(* Skipping definition `Spec.ExecuteV.replicate_machineInt' *)

Definition zeroToExclusive_machineInt {t : Type} `{Utility.Utility.MachineWidth
  t}
   : Utility.Utility.MachineInt -> list t :=
  fun max =>
    Coq.Lists.List.map (Utility.Utility.fromImm) (rangeNonNegZ 0 (Z.sub max 1)).

(* Skipping definition `Spec.ExecuteV.length_machineInt' *)

(* Skipping definition `Spec.ExecuteV.index_machineInt' *)

(* Skipping definition `Spec.ExecuteV.testBit_machineInt' *)

(* Skipping definition `Spec.ExecuteV.int8_toWord8' *)

(* Skipping definition `Spec.ExecuteV.word8_toInt8' *)

Definition translateLMUL
   : Utility.Utility.MachineInt -> option Utility.Utility.MachineInt :=
  fun enc =>
    let dec :=
      if Z.eqb enc 5 : bool then Some (Z.neg 3) else
      if Z.eqb enc 6 : bool then Some (Z.neg 2) else
      if Z.eqb enc 7 : bool then Some (Z.neg 1) else
      if Z.eqb enc 0 : bool then Some (0) else
      if Z.eqb enc 1 : bool then Some 1 else
      if Z.eqb enc 2 : bool then Some 2 else
      if Z.eqb enc 3 : bool then Some 3 else
      None in
    dec.

Definition translateWidth_Vtype
   : Utility.Utility.MachineInt -> option Utility.Utility.MachineInt :=
  fun enc =>
    let dec :=
      if Z.eqb enc 0 : bool then Some 3 else
      if Z.eqb enc 1 : bool then Some 4 else
      if Z.eqb enc 2 : bool then Some 5 else
      if Z.eqb enc 3 : bool then Some 6 else
      None in
    dec.

Definition translateWidth_Inst
   : Utility.Utility.MachineInt -> option Utility.Utility.MachineInt :=
  fun enc =>
    let dec :=
      if Z.eqb enc 0 : bool then Some 3 else
      if Z.eqb enc 5 : bool then Some 4 else
      if Z.eqb enc 6 : bool then Some 5 else
      if Z.eqb enc 7 : bool then Some 6 else
      None in
    dec.

Definition translateNumFields
   : Utility.Utility.MachineInt -> option Utility.Utility.MachineInt :=
  fun enc =>
    let dec :=
      if Z.eqb enc 0 : bool then Some 1 else
      if Z.eqb enc 1 : bool then Some 2 else
      if Z.eqb enc 2 : bool then Some 3 else
      if Z.eqb enc 3 : bool then Some 4 else
      if Z.eqb enc 4 : bool then Some 5 else
      if Z.eqb enc 5 : bool then Some 6 else
      if Z.eqb enc 6 : bool then Some 7 else
      if Z.eqb enc 7 : bool then Some 8 else
      None in
    dec.

Definition legalSEW
   : Utility.Utility.MachineInt ->
     Utility.Utility.MachineInt -> Utility.Utility.MachineInt -> bool :=
  fun vsew vlmul vlenb =>
    match Bind (translateWidth_Vtype vsew) (fun pow2SEW =>
                  Bind (translateLMUL vlmul) (fun pow2LMUL =>
                          (Return (Z.leb (Z.pow 2 pow2SEW) (Z.pow 2 pow2LMUL * vlenb * 8))))) with
    | Some y' => y'
    | None => false
    end.

Definition consistentRatio
   : Utility.Utility.MachineInt ->
     Utility.Utility.MachineInt ->
     Utility.Utility.MachineInt -> Utility.Utility.MachineInt -> bool :=
  fun vlmul vsew vlmul' vsew' =>
    match Bind (translateWidth_Vtype vsew) (fun pow2SEW =>
                  Bind (translateLMUL vlmul) (fun pow2LMUL =>
                          Bind (translateWidth_Vtype vsew') (fun pow2SEW' =>
                                  Bind (translateLMUL vlmul') (fun pow2LMUL' =>
                                          Return (Z.eqb (Z.sub pow2SEW pow2LMUL) (Z.sub pow2SEW' pow2LMUL')))))) with
    | Some y' => y'
    | None => false
    end.

Definition computeVLMAX
   : Utility.Utility.MachineInt ->
     Utility.Utility.MachineInt ->
     Utility.Utility.MachineInt -> Utility.Utility.MachineInt :=
  fun vlmul vsew vlenb =>
    match Bind (translateWidth_Vtype vsew) (fun pow2SEW =>
                  Bind (translateLMUL vlmul) (fun pow2LMUL =>
                          (let exp := Z.sub (Z.add 3 pow2LMUL) pow2SEW in
                           if Z.geb exp 0 : bool
                           then Return (vlenb * Z.pow 2 exp)
                           else Return (Z.quot vlenb (Z.pow 2 (Z.neg exp)))))) with
    | Some y' => y'
    | None => 0
    end.

Definition computeMaxTail
   : Utility.Utility.MachineInt ->
     Utility.Utility.MachineInt ->
     Utility.Utility.MachineInt -> Utility.Utility.MachineInt :=
  fun vlmul vlenb vsew =>
    match Bind (translateWidth_Vtype vsew) (fun pow2SEW =>
                  Bind (translateLMUL vlmul) (fun pow2LMUL =>
                          let tail :=
                            8 * vlenb *
                            Z.pow 2 (Z.sub (if Z.ltb pow2LMUL 0 : bool then 0 else pow2LMUL) pow2SEW) in
                          if Z.geb tail 1 : bool
                          then Return tail
                          else Return 0)) with
    | Some y' => y'
    | None => 0
    end.

Definition executeVset {p : Type -> Type} {t : Type} `{Spec.Machine.RiscvMachine
  p t}
   : bool ->
     Utility.Utility.MachineInt ->
     Utility.Utility.MachineInt -> Spec.Decode.Register -> p unit :=
  fun noRatioCheck avl vtypei rd =>
    let vma := (Utility.Utility.bitSlice vtypei 7 8) in
    let vta := (Utility.Utility.bitSlice vtypei 6 7) in
    let vsew := (Utility.Utility.bitSlice vtypei 3 6) in
    let vlmul := (Utility.Utility.bitSlice vtypei 0 3) in
    Bind (Spec.Machine.getCSRField Spec.CSRField.VLMul) (fun vlmul_old =>
            Bind (Spec.Machine.getCSRField Spec.CSRField.VSEW) (fun vsew_old =>
                    Bind (Spec.Machine.getCSRField Spec.CSRField.VLenB) (fun vlenb =>
                            Bind (Spec.Machine.setCSRField Spec.CSRField.VLMul vlmul) (fun _ =>
                                    Bind (Spec.Machine.setCSRField Spec.CSRField.VSEW vsew) (fun _ =>
                                            Bind (Spec.Machine.setCSRField Spec.CSRField.VMA vma) (fun _ =>
                                                    Bind (Spec.Machine.setCSRField Spec.CSRField.VTA vta) (fun _ =>
                                                            let vlmax :=
                                                              computeVLMAX vlmul vsew (Utility.Utility.fromImm vlenb) in
                                                            let vl :=
                                                              (if Z.leb avl vlmax : bool
                                                               then (avl)
                                                               else vlmax) in
                                                            let vill :=
                                                              (if (andb (legalSEW vsew vlmul vlenb) (orb noRatioCheck
                                                                                                         (consistentRatio
                                                                                                          (Utility.Utility.fromImm
                                                                                                           vlmul_old)
                                                                                                          (Utility.Utility.fromImm
                                                                                                           vsew_old)
                                                                                                          vlmul
                                                                                                          vsew))) : bool
                                                               then 0
                                                               else 1) in
                                                            Bind (Spec.Machine.setCSRField Spec.CSRField.VL vl)
                                                                 (fun _ =>
                                                                    Bind (Spec.Machine.setCSRField Spec.CSRField.VStart
                                                                                                   0) (fun _ =>
                                                                            Bind (Spec.Machine.setCSRField
                                                                                  Spec.CSRField.VIll vill) (fun _ =>
                                                                                    unless (Z.eqb rd 0)
                                                                                           (Spec.Machine.setRegister rd
                                                                                            (Utility.Utility.fromImm
                                                                                             vl)))))))))))).

Definition getVRegisterElement {p : Type -> Type} {t : Type}
  `{Spec.Machine.RiscvMachine p t}
   : Utility.Utility.MachineInt ->
     Spec.Decode.VRegister -> Utility.Utility.MachineInt -> p (list byte) :=
  fun eew baseReg eltIndex =>
    if (orb (Z.eqb eew 1) (orb (Z.eqb eew 2) (orb (Z.eqb eew 4) (Z.eqb eew
                                                                       8)))) : bool
    then Spec.Machine.raiseException 0 2
    else Bind (Spec.Machine.getCSRField Spec.CSRField.VLenB) (fun vlenb =>
                 Bind (Spec.Machine.getVRegister baseReg) (fun vregValue =>
                         let value := upto eew (from (eltIndex * eew) vregValue) in
                         if Z.eqb (len value) eew : bool
                         then Return value
                         else Spec.Machine.raiseException 0 2)).

Definition setVRegisterElement {p : Type -> Type} {t : Type}
  `{Spec.Machine.RiscvMachine p t}
   : Utility.Utility.MachineInt ->
     Spec.Decode.VRegister -> Utility.Utility.MachineInt -> list byte -> p unit :=
  fun eew baseReg eltIndex value =>
    if (orb (Z.eqb eew 1) (orb (Z.eqb eew 2) (orb (Z.eqb eew 4) (Z.eqb eew
                                                                       8)))) : bool
    then Spec.Machine.raiseException 0 2
    else Bind (Spec.Machine.getCSRField Spec.CSRField.VLenB) (fun vlenb =>
                 Bind (Spec.Machine.getVRegister baseReg) (fun vregValue =>
                         let newVregValue :=
                           Coq.Init.Datatypes.app (upto (eltIndex * eew) vregValue) (Coq.Init.Datatypes.app
                                                   (value) (from (Z.add eltIndex 1 * eew) vregValue)) in
                         if Z.eqb (len newVregValue) (len vregValue) : bool
                         then (Spec.Machine.setVRegister baseReg newVregValue)
                         else Spec.Machine.raiseException 0 2)).

Definition loadUntranslatedBytes {p : Type -> Type} {t : Type}
  `{Spec.Machine.RiscvMachine p t}
   : t -> Utility.Utility.MachineInt -> p (list byte) :=
  fun memAddr numBytes =>
    (forM (zeroToExclusive_machineInt numBytes) (fun i =>
             Bind (Spec.VirtualMemory.translate Spec.Machine.Load 1 (Z.add memAddr
                                                                           (Utility.Utility.fromImm i))) (fun addr =>
                     Spec.Machine.loadByte Spec.Machine.Execute addr))).

Definition storeUntranslatedBytes {p : Type -> Type} {t : Type}
  `{Spec.Machine.RiscvMachine p t}
   : t -> list byte -> p unit :=
  fun memAddr value =>
    forM_ (zeroToExclusive_machineInt (len value)) (fun i =>
             Bind (Spec.VirtualMemory.translate Spec.Machine.Store 1 (Z.add memAddr
                                                                            (Utility.Utility.fromImm i))) (fun addr =>
                     (Spec.Machine.storeByte Spec.Machine.Execute addr ((get value i))))).

Definition testVectorBit : list byte -> Utility.Utility.MachineInt -> bool :=
  fun vregValue posn => Z.testbit.

Definition execute {p : Type -> Type} {t : Type} `{Spec.Machine.RiscvMachine p
                                                                             t}
   : Spec.Decode.InstructionV -> p unit :=
  fun arg_0__ =>
    match arg_0__ with
    | Spec.Decode.Vsetvli rd rs1 vtypei =>
        Bind (Spec.Machine.getCSRField Spec.CSRField.VL) (fun old_vl =>
                if Z.eqb rs1 0 : bool
                then Bind (Spec.Machine.getRegister rs1) (fun avl =>
                             executeVset false (Utility.Utility.regToInt64 avl) vtypei rd)
                else if Z.eqb rd 0 : bool
                     then executeVset false (Utility.Utility.regToInt64
                                             (Utility.Utility.maxSigned : t)) vtypei rd
                     else executeVset true (Utility.Utility.regToInt64
                                            (Utility.Utility.maxSigned : t)) vtypei rd)
    | Spec.Decode.Vsetvl rd rs1 rs2 =>
        Bind (Spec.Machine.getRegister rs2) (fun vtypei =>
                Bind (Spec.Machine.getCSRField Spec.CSRField.VL) (fun old_vl =>
                        if Z.eqb rs1 0 : bool
                        then Bind (Spec.Machine.getRegister rs1) (fun avl =>
                                     executeVset false (Utility.Utility.regToInt64 avl) (Utility.Utility.regToInt64
                                                                                         vtypei) rd)
                        else if Z.eqb rd 0 : bool
                             then executeVset false (Utility.Utility.regToInt64
                                                     (Utility.Utility.maxSigned : t)) (Utility.Utility.regToInt64
                                                                                       vtypei) rd
                             else executeVset true old_vl (Utility.Utility.regToInt64 vtypei) rd))
    | Spec.Decode.Vsetivli rd uimm vtypei => executeVset false uimm vtypei rd
    | Spec.Decode.Vle width vd rs1 vm =>
        Bind (Spec.Machine.getCSRField Spec.CSRField.VStart) (fun vstart =>
                Bind (Spec.Machine.getCSRField Spec.CSRField.VLMul) (fun vlmul =>
                        Bind (Spec.Machine.getCSRField Spec.CSRField.VLenB) (fun vlenb =>
                                Bind (Spec.Machine.getCSRField Spec.CSRField.VL) (fun vl =>
                                        Bind (Spec.Machine.getCSRField Spec.CSRField.VMA) (fun vma =>
                                                Bind (Spec.Machine.getCSRField Spec.CSRField.VTA) (fun vta =>
                                                        Bind (Spec.Machine.getVRegister 0) (fun vmask =>
                                                                let eew :=
                                                                  Z.pow 2 (match translateWidth_Inst width with
                                                                         | Some y' => y'
                                                                         | None => 8
                                                                         end) in
                                                                let maxTail := computeMaxTail vlmul vlenb (eew) in
                                                                let eltsPerVReg := Z.quot (vlenb * 8) eew in
                                                                Bind (forM_ (rangeNonNegZ vstart (Z.sub vl 1)) (fun i =>
                                                                               let realEltIdx :=
                                                                                 (Z.quot i eltsPerVReg) in
                                                                               let realVd :=
                                                                                 Z.add vd (Z.quot i eltsPerVReg) in
                                                                               Bind (Spec.Machine.getRegister rs1)
                                                                                    (fun baseMem =>
                                                                                       Bind (loadUntranslatedBytes
                                                                                             (Z.add baseMem
                                                                                                    (Utility.Utility.fromImm
                                                                                                     (i *
                                                                                                      Z.quot eew 8)))
                                                                                             (Z.quot eew 8)) (fun mem =>
                                                                                               Bind (when (orb (Z.eqb vm
                                                                                                                      1)
                                                                                                               (testVectorBit
                                                                                                                vmask
                                                                                                                (i)))
                                                                                                          ((setVRegisterElement
                                                                                                            (Utility.Utility.fromImm
                                                                                                             ((Z.quot
                                                                                                               eew 8)))
                                                                                                            (Utility.Utility.fromImm
                                                                                                             (realVd))
                                                                                                            (Utility.Utility.fromImm
                                                                                                             (realEltIdx))
                                                                                                            mem)))
                                                                                                    (fun _ =>
                                                                                                       Bind (when (andb
                                                                                                                   (Z.eqb
                                                                                                                    vm
                                                                                                                    0)
                                                                                                                   (andb
                                                                                                                    (negb
                                                                                                                     (testVectorBit
                                                                                                                      vmask
                                                                                                                      (i)))
                                                                                                                    (Z.eqb
                                                                                                                     vma
                                                                                                                     1)))
                                                                                                                  (setVRegisterElement
                                                                                                                   (Utility.Utility.fromImm
                                                                                                                    ((Z.quot
                                                                                                                      eew
                                                                                                                      8)))
                                                                                                                   (Utility.Utility.fromImm
                                                                                                                    (realVd))
                                                                                                                   (Utility.Utility.fromImm
                                                                                                                    (realEltIdx))
                                                                                                                   (repeat
                                                                                                                    (Z.quot
                                                                                                                     eew
                                                                                                                     8)
                                                                                                                    yx)))
                                                                                                            (fun _ =>
                                                                                                               Spec.Machine.setCSRField
                                                                                                               Spec.CSRField.VStart
                                                                                                               i))))))
                                                                     (fun _ =>
                                                                        Bind (when (Z.eqb vta 1) (forM_ (rangeNonNegZ vl
                                                                                                                      (Z.sub
                                                                                                                       maxTail
                                                                                                                       1))
                                                                                                        (fun i =>
                                                                                                           let realEltIdx :=
                                                                                                             (Z.quot i
                                                                                                                     eltsPerVReg) in
                                                                                                           let realVd :=
                                                                                                             Z.add vd
                                                                                                                   ((Z.quot
                                                                                                                     i
                                                                                                                     eltsPerVReg)) in
                                                                                                           (setVRegisterElement
                                                                                                            (Utility.Utility.fromImm
                                                                                                             ((Z.quot
                                                                                                               eew 8)))
                                                                                                            (Utility.Utility.fromImm
                                                                                                             (realVd))
                                                                                                            (Utility.Utility.fromImm
                                                                                                             (realEltIdx))
                                                                                                            (repeat
                                                                                                             (Z.quot eew
                                                                                                                     8)
                                                                                                             yx)))))
                                                                             (fun _ =>
                                                                                Spec.Machine.setCSRField
                                                                                Spec.CSRField.VStart 0)))))))))
    | Spec.Decode.Vaddvv vd vs1 vs2 vm =>
        Bind (Spec.Machine.getCSRField Spec.CSRField.VStart) (fun vstart =>
                Bind (Spec.Machine.getCSRField Spec.CSRField.VLMul) (fun vlmul =>
                        Bind (Spec.Machine.getCSRField Spec.CSRField.VLenB) (fun vlenb =>
                                Bind (Spec.Machine.getCSRField Spec.CSRField.VL) (fun vl =>
                                        Bind (Spec.Machine.getCSRField Spec.CSRField.VMA) (fun vma =>
                                                Bind (Spec.Machine.getCSRField Spec.CSRField.VTA) (fun vta =>
                                                        Bind (Spec.Machine.getCSRField Spec.CSRField.VSEW) (fun vsew =>
                                                                Bind (Spec.Machine.getVRegister 0) (fun vmask =>
                                                                        let eew :=
                                                                          Z.pow 2 (match translateWidth_Vtype vsew with
                                                                                 | Some y' => y'
                                                                                 | None => 0
                                                                                 end) in
                                                                        let maxTail :=
                                                                          computeMaxTail vlmul vlenb (eew) in
                                                                        let eltsPerVReg := Z.quot (vlenb * 8) eew in
                                                                        Bind (forM_ (rangeNonNegZ vstart (Z.sub vl 1))
                                                                                    (fun i =>
                                                                                       let realEltIdx :=
                                                                                         (Z.quot i eltsPerVReg) in
                                                                                       let realVs2 :=
                                                                                         Z.add vs2 ((Z.quot i
                                                                                                            eltsPerVReg)) in
                                                                                       let realVs1 :=
                                                                                         Z.add vs1 ((Z.quot i
                                                                                                            eltsPerVReg)) in
                                                                                       let realVd :=
                                                                                         Z.add vd ((Z.quot i
                                                                                                           eltsPerVReg)) in
                                                                                       Bind (getVRegisterElement
                                                                                             (Utility.Utility.fromImm
                                                                                              (Z.quot eew 8))
                                                                                             (Utility.Utility.fromImm
                                                                                              (realVs1))
                                                                                             (Utility.Utility.fromImm
                                                                                              (realEltIdx)))
                                                                                            (fun vs1value =>
                                                                                               Bind (getVRegisterElement
                                                                                                     (Utility.Utility.fromImm
                                                                                                      (Z.quot eew 8))
                                                                                                     (Utility.Utility.fromImm
                                                                                                      (realVs2))
                                                                                                     (Utility.Utility.fromImm
                                                                                                      (realEltIdx)))
                                                                                                    (fun vs2value =>
                                                                                                       let vs2Element :=
                                                                                                         ((Utility.Utility.combineBytes : list
                                                                                                           byte ->
                                                                                                           Utility.Utility.MachineInt)
                                                                                                          (Coq.Lists.List.map
                                                                                                           int8_toWord8
                                                                                                           vs2value)) in
                                                                                                       let vs1Element :=
                                                                                                         ((Utility.Utility.combineBytes : list
                                                                                                           byte ->
                                                                                                           Utility.Utility.MachineInt)
                                                                                                          (Coq.Lists.List.map
                                                                                                           int8_toWord8
                                                                                                           vs1value)) in
                                                                                                       let vdElement :=
                                                                                                         Z.add
                                                                                                         vs1Element
                                                                                                         vs2Element in
                                                                                                       Bind
                                                                                                       (Spec.Machine.setCSRField
                                                                                                        Spec.CSRField.VStart
                                                                                                        i) (fun _ =>
                                                                                                          Bind (when
                                                                                                                (orb
                                                                                                                 (Z.eqb
                                                                                                                  vm 1)
                                                                                                                 (testVectorBit
                                                                                                                  vmask
                                                                                                                  i))
                                                                                                                (setVRegisterElement
                                                                                                                 (Utility.Utility.fromImm
                                                                                                                  (Z.quot
                                                                                                                   eew
                                                                                                                   8))
                                                                                                                 (Utility.Utility.fromImm
                                                                                                                  (realVd))
                                                                                                                 (Utility.Utility.fromImm
                                                                                                                  (realEltIdx))
                                                                                                                 (Coq.Lists.List.map
                                                                                                                  word8_toInt8
                                                                                                                  (Utility.Utility.splitBytes
                                                                                                                   (eew)
                                                                                                                   vdElement))))
                                                                                                               (fun _ =>
                                                                                                                  Bind
                                                                                                                  (when
                                                                                                                   (andb
                                                                                                                    (Z.eqb
                                                                                                                     vm
                                                                                                                     0)
                                                                                                                    (andb
                                                                                                                     (negb
                                                                                                                      (testVectorBit
                                                                                                                       vmask
                                                                                                                       i))
                                                                                                                     (Z.eqb
                                                                                                                      vma
                                                                                                                      1)))
                                                                                                                   (setVRegisterElement
                                                                                                                    (Utility.Utility.fromImm
                                                                                                                     ((Z.quot
                                                                                                                       eew
                                                                                                                       8)))
                                                                                                                    (Utility.Utility.fromImm
                                                                                                                     (realVd))
                                                                                                                    (Utility.Utility.fromImm
                                                                                                                     (realEltIdx))
                                                                                                                    (repeat
                                                                                                                     (Z.quot
                                                                                                                      eew
                                                                                                                      8)
                                                                                                                     yx)))
                                                                                                                  (fun _ =>
                                                                                                                     Spec.Machine.setCSRField
                                                                                                                     Spec.CSRField.VStart
                                                                                                                     i)))))))
                                                                             (fun _ =>
                                                                                Bind (when (Z.eqb vta 1) (forM_
                                                                                            (rangeNonNegZ vl (Z.sub
                                                                                                           maxTail 1))
                                                                                            (fun i =>
                                                                                               let realEltIdx :=
                                                                                                 (Z.quot i
                                                                                                         eltsPerVReg) in
                                                                                               let realVd :=
                                                                                                 Z.add vd ((Z.quot i
                                                                                                                   eltsPerVReg)) in
                                                                                               setVRegisterElement
                                                                                               (Utility.Utility.fromImm
                                                                                                ((Z.quot eew 8)))
                                                                                               (Utility.Utility.fromImm
                                                                                                (realVd))
                                                                                               (Utility.Utility.fromImm
                                                                                                (realEltIdx)) (repeat
                                                                                                               (Z.quot
                                                                                                                eew 8)
                                                                                                               yx))))
                                                                                     (fun _ =>
                                                                                        Spec.Machine.setCSRField
                                                                                        Spec.CSRField.VStart 0))))))))))
    | Spec.Decode.Vse width vd rs1 vm =>
        Bind (Spec.Machine.getCSRField Spec.CSRField.VStart) (fun vstart =>
                Bind (Spec.Machine.getCSRField Spec.CSRField.VLMul) (fun vlmul =>
                        Bind (Spec.Machine.getCSRField Spec.CSRField.VLenB) (fun vlenb =>
                                Bind (Spec.Machine.getCSRField Spec.CSRField.VL) (fun vl =>
                                        Bind (Spec.Machine.getCSRField Spec.CSRField.VMA) (fun vma =>
                                                Bind (Spec.Machine.getCSRField Spec.CSRField.VTA) (fun vta =>
                                                        Bind (Spec.Machine.getVRegister 0) (fun vmask =>
                                                                let eew :=
                                                                  Z.pow 2 (match translateWidth_Inst width with
                                                                         | Some y' => y'
                                                                         | None => 8
                                                                         end) in
                                                                let maxTail := computeMaxTail vlmul vlenb (eew) in
                                                                let eltsPerVReg := Z.quot (vlenb * 8) eew in
                                                                Bind (forM_ (rangeNonNegZ vstart (Z.sub vl 1)) (fun i =>
                                                                               let realEltIdx :=
                                                                                 (Z.quot i eltsPerVReg) in
                                                                               let realVd :=
                                                                                 Z.add vd ((Z.quot i eltsPerVReg)) in
                                                                               Bind (Spec.Machine.getRegister rs1)
                                                                                    (fun baseMem =>
                                                                                       Bind (getVRegisterElement
                                                                                             (Utility.Utility.fromImm
                                                                                              ((Z.quot eew 8)))
                                                                                             (Utility.Utility.fromImm
                                                                                              (realVd))
                                                                                             (Utility.Utility.fromImm
                                                                                              (realEltIdx)))
                                                                                            (fun value =>
                                                                                               Bind
                                                                                               (storeUntranslatedBytes
                                                                                                (Z.add baseMem
                                                                                                       (Utility.Utility.fromImm
                                                                                                        (i *
                                                                                                         Z.quot eew 8)))
                                                                                                value) (fun _ =>
                                                                                                  Spec.Machine.setCSRField
                                                                                                  Spec.CSRField.VStart
                                                                                                  i))))) (fun _ =>
                                                                        Spec.Machine.setCSRField Spec.CSRField.VStart
                                                                                                 0))))))))
    | Spec.Decode.Vlr vd rs1 nf =>
        let numFields :=
          match translateNumFields nf with
          | Some y' => y'
          | None => 9
          end in
        Bind (Spec.Machine.getCSRField Spec.CSRField.VLenB) (fun vlenb =>
                when (andb (orb (Z.eqb numFields 1) (orb (Z.eqb numFields 2) (orb (Z.eqb
                                                                                   numFields 4) (Z.eqb numFields 8))))
                           (Z.eqb (Z.quot vd numFields) 0)) (forM_ (rangeNonNegZ 0 (Z.sub numFields 1))
                                                                   (fun i =>
                                                                      Bind (Spec.Machine.getRegister rs1)
                                                                           (fun baseMem =>
                                                                              Bind (loadUntranslatedBytes (Z.add baseMem
                                                                                                                 (Utility.Utility.fromImm
                                                                                                                  (vlenb
                                                                                                                   *
                                                                                                                   i)))
                                                                                                          (vlenb))
                                                                                   (fun mem =>
                                                                                      Spec.Machine.setVRegister (Z.add
                                                                                                                 vd (i))
                                                                                      mem)))))
    | Spec.Decode.Vsr vs3 rs1 nf =>
        let numFields :=
          match translateNumFields nf with
          | Some y' => y'
          | None => 9
          end in
        Bind (Spec.Machine.getCSRField Spec.CSRField.VLenB) (fun vlenb =>
                when (andb (orb (Z.eqb numFields 1) (orb (Z.eqb numFields 2) (orb (Z.eqb
                                                                                   numFields 4) (Z.eqb numFields 8))))
                           (Z.eqb (Z.quot vs3 numFields) 0)) (forM_ (rangeNonNegZ 0 (Z.sub numFields 1))
                                                                    (fun i =>
                                                                       Bind (Spec.Machine.getRegister rs1)
                                                                            (fun baseMem =>
                                                                               Bind (Spec.Machine.getVRegister (Z.add
                                                                                                                vs3
                                                                                                                (i)))
                                                                                    (fun value =>
                                                                                       storeUntranslatedBytes (Z.add
                                                                                                               baseMem
                                                                                                               (Utility.Utility.fromImm
                                                                                                                (vlenb *
                                                                                                                 i)))
                                                                                       value)))))
    | inst => Return tt
    end.

(* External variables:
     Bind None Return Some Type Z.add Z.eqb Z.geb Z.leb Z.ltb Z.neg Z.pow Z.sub
     Z.testbit andb bool byte false forM forM_ from get int8_toWord8 len list negb
     op_zt__ option orb rangeNonNegZ repeat true tt unit unless upto when
     word8_toInt8 yx Coq.Init.Datatypes.app Coq.Lists.List.map Spec.CSRField.VIll
     Spec.CSRField.VL Spec.CSRField.VLMul Spec.CSRField.VLenB Spec.CSRField.VMA
     Spec.CSRField.VSEW Spec.CSRField.VStart Spec.CSRField.VTA
     Spec.Decode.InstructionV Spec.Decode.Register Spec.Decode.VRegister
     Spec.Decode.Vaddvv Spec.Decode.Vle Spec.Decode.Vlr Spec.Decode.Vse
     Spec.Decode.Vsetivli Spec.Decode.Vsetvl Spec.Decode.Vsetvli Spec.Decode.Vsr
     Spec.Machine.Execute Spec.Machine.Load Spec.Machine.RiscvMachine
     Spec.Machine.Store Spec.Machine.getCSRField Spec.Machine.getRegister
     Spec.Machine.getVRegister Spec.Machine.loadByte Spec.Machine.raiseException
     Spec.Machine.setCSRField Spec.Machine.setRegister Spec.Machine.setVRegister
     Spec.Machine.storeByte Spec.VirtualMemory.translate Utility.Utility.MachineInt
     Utility.Utility.MachineWidth Utility.Utility.bitSlice
     Utility.Utility.combineBytes Utility.Utility.fromImm Utility.Utility.maxSigned
     Utility.Utility.regToInt64 Utility.Utility.splitBytes Z.quot
*)
