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
Local Open Scope Z.
Require Import riscv.Utility.Utility.

(* Converted imports: *)

Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Import Coq.ZArith.BinInt.
Require GHC.Base.
Require GHC.Err.
Require GHC.Num.
Require Import Monads.
Require Spec.CSRField.
Require Spec.Decode.
Require Spec.Machine.
Require Spec.VirtualMemory.
Require Import Utility.
Require Utility.Utility.
Require Z.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

(* Skipping definition `Spec.ExecuteV.take_machineInt' *)

(* Skipping definition `Spec.ExecuteV.drop_machineInt' *)

(* Skipping definition `Spec.ExecuteV.replicate_machineInt' *)

Definition zeroToExclusive_machineInt {t : Type} `{Utility.Utility.MachineWidth
  t}
   : Z -> list t :=
  fun max =>
    Coq.Lists.List.map (Utility.Utility.fromImm) (rangeNonNegZ 0 (max - 1)).

(* Skipping definition `Spec.ExecuteV.length_machineInt' *)

(* Skipping definition `Spec.ExecuteV.index_machineInt' *)

(* Skipping definition `Spec.ExecuteV.testBit_machineInt' *)

(* Skipping definition `Spec.ExecuteV.int8_toWord8' *)

(* Skipping definition `Spec.ExecuteV.word8_toInt8' *)

Definition translateLMUL : Z -> option Z :=
  fun arg_0__ =>
    let 'num_1__ := arg_0__ in
    if num_1__ GHC.Base.== #5 : bool then Some (negate 3) else
    let 'num_2__ := arg_0__ in
    if num_2__ GHC.Base.== #6 : bool then Some (negate 2) else
    let 'num_3__ := arg_0__ in
    if num_3__ GHC.Base.== #7 : bool then Some (negate 1) else
    let 'num_4__ := arg_0__ in
    if num_4__ GHC.Base.== #0 : bool then Some (0) else
    let 'num_5__ := arg_0__ in
    if num_5__ GHC.Base.== #1 : bool then Some 1 else
    let 'num_6__ := arg_0__ in
    if num_6__ GHC.Base.== #2 : bool then Some 2 else
    let 'num_7__ := arg_0__ in
    if num_7__ GHC.Base.== #3 : bool then Some 3 else
    None.

Definition translateWidth_Vtype : Z -> option Z :=
  fun arg_0__ =>
    let 'num_1__ := arg_0__ in
    if num_1__ GHC.Base.== #0 : bool then Some 3 else
    let 'num_2__ := arg_0__ in
    if num_2__ GHC.Base.== #1 : bool then Some 4 else
    let 'num_3__ := arg_0__ in
    if num_3__ GHC.Base.== #2 : bool then Some 5 else
    let 'num_4__ := arg_0__ in
    if num_4__ GHC.Base.== #3 : bool then Some 6 else
    None.

Definition translateWidth_Inst : Z -> option Z :=
  fun arg_0__ =>
    let 'num_1__ := arg_0__ in
    if num_1__ GHC.Base.== #0 : bool then Some 3 else
    let 'num_2__ := arg_0__ in
    if num_2__ GHC.Base.== #5 : bool then Some 4 else
    let 'num_3__ := arg_0__ in
    if num_3__ GHC.Base.== #6 : bool then Some 5 else
    let 'num_4__ := arg_0__ in
    if num_4__ GHC.Base.== #7 : bool then Some 6 else
    None.

Definition translateNumFields : Z -> option Z :=
  fun arg_0__ =>
    let 'num_1__ := arg_0__ in
    if num_1__ GHC.Base.== #0 : bool then Some 1 else
    let 'num_2__ := arg_0__ in
    if num_2__ GHC.Base.== #1 : bool then Some 2 else
    let 'num_3__ := arg_0__ in
    if num_3__ GHC.Base.== #2 : bool then Some 3 else
    let 'num_4__ := arg_0__ in
    if num_4__ GHC.Base.== #3 : bool then Some 4 else
    let 'num_5__ := arg_0__ in
    if num_5__ GHC.Base.== #4 : bool then Some 5 else
    let 'num_6__ := arg_0__ in
    if num_6__ GHC.Base.== #5 : bool then Some 6 else
    let 'num_7__ := arg_0__ in
    if num_7__ GHC.Base.== #6 : bool then Some 7 else
    let 'num_8__ := arg_0__ in
    if num_8__ GHC.Base.== #7 : bool then Some 8 else
    None.

Definition legalSEW : Z -> Z -> Z -> bool :=
  fun vsew vlmul vlenb =>
    match Bind (translateWidth_Vtype vsew) (fun pow2SEW =>
                  Bind (translateLMUL vlmul) (fun pow2LMUL =>
                          (Return (Z.pow 2 pow2SEW GHC.Base.<= (Z.pow 2 pow2LMUL * vlenb * 8))))) with
    | Some y' => y'
    | None => false
    end.

Definition consistentRatio : Z -> Z -> Z -> Z -> bool :=
  fun vlmul vsew vlmul' vsew' =>
    match Bind (translateWidth_Vtype vsew) (fun pow2SEW =>
                  Bind (translateLMUL vlmul) (fun pow2LMUL =>
                          Bind (translateWidth_Vtype vsew') (fun pow2SEW' =>
                                  Bind (translateLMUL vlmul') (fun pow2LMUL' =>
                                          Return (Z.eqb (pow2SEW - pow2LMUL) (pow2SEW' - pow2LMUL')))))) with
    | Some y' => y'
    | None => false
    end.

Definition computeVLMAX : Z -> Z -> Z -> Z :=
  fun vlmul vsew vlenb =>
    match Bind (translateWidth_Vtype vsew) (fun pow2SEW =>
                  Bind (translateLMUL vlmul) (fun pow2LMUL =>
                          (let exp := 3 + pow2LMUL - pow2SEW in
                           if exp GHC.Base.>= 0 : bool
                           then Return (vlenb * Z.pow 2 exp)
                           else Return (div vlenb (Z.pow 2 (negate exp)))))) with
    | Some y' => y'
    | None => 0
    end.

Definition computeMaxTail : Z -> Z -> Z -> Z :=
  fun vlmul vlenb vsew =>
    match Bind (translateWidth_Vtype vsew) (fun pow2SEW =>
                  Bind (translateLMUL vlmul) (fun pow2LMUL =>
                          let tail :=
                            8 * vlenb *
                            Z.pow 2 ((if pow2LMUL GHC.Base.< 0 : bool then 0 else pow2LMUL) - pow2SEW) in
                          if tail GHC.Base.>= 1 : bool
                          then Return tail
                          else Return 0)) with
    | Some y' => y'
    | None => 0
    end.

Definition executeVset {p : Type -> Type} {t : Type} `{Spec.Machine.RiscvMachine
  p t}
   : bool -> Z -> Z -> Spec.Decode.Register -> p unit :=
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
                                                              (if (avl) GHC.Base.<= vlmax : bool
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
   : Z -> Spec.Decode.VRegister -> Z -> p (list byte) :=
  fun eew baseReg eltIndex =>
    if (forallb (fun x => x) (cons (negb (Z.eqb eew 1)) (cons (negb (Z.eqb eew 2))
                                                              (cons (negb (Z.eqb eew 4)) (cons (negb (Z.eqb eew 8))
                                                                                               nil))))) : bool
    then Spec.Machine.raiseException 0 2
    else Bind (Spec.Machine.getCSRField Spec.CSRField.VLenB) (fun vlenb =>
                 Bind (Spec.Machine.getVRegister baseReg) (fun vregValue =>
                         let value := upto eew (from (eltIndex * eew) vregValue) in
                         if Z.eqb (len value) eew : bool
                         then Return value
                         else Spec.Machine.raiseException 0 2)).

Definition setVRegisterElement {p : Type -> Type} {t : Type}
  `{Spec.Machine.RiscvMachine p t}
   : Z -> Spec.Decode.VRegister -> Z -> list byte -> p unit :=
  fun eew baseReg eltIndex value =>
    if (forallb (fun x => x) (cons (negb (Z.eqb eew 1)) (cons (negb (Z.eqb eew 2))
                                                              (cons (negb (Z.eqb eew 4)) (cons (negb (Z.eqb eew 8))
                                                                                               nil))))) : bool
    then Spec.Machine.raiseException 0 2
    else Bind (Spec.Machine.getCSRField Spec.CSRField.VLenB) (fun vlenb =>
                 Bind (Spec.Machine.getVRegister baseReg) (fun vregValue =>
                         let newVregValue :=
                           Coq.Init.Datatypes.app (upto (eltIndex * eew) vregValue) (Coq.Init.Datatypes.app
                                                   (value) (from ((eltIndex + 1) * eew) vregValue)) in
                         if Z.eqb (len newVregValue) (len vregValue) : bool
                         then (Spec.Machine.setVRegister baseReg newVregValue)
                         else Spec.Machine.raiseException 0 2)).

Definition loadUntranslatedBytes {p : Type -> Type} {t : Type}
  `{Spec.Machine.RiscvMachine p t}
   : t -> Z -> p (list byte) :=
  fun memAddr numBytes =>
    (forM (zeroToExclusive_machineInt numBytes) (fun i =>
             Bind (Spec.VirtualMemory.translate Spec.Machine.Load 1 (memAddr +
                                                 Utility.Utility.fromImm i)) (fun addr =>
                     Spec.Machine.loadByte Spec.Machine.Execute addr))).

Definition storeUntranslatedBytes {p : Type -> Type} {t : Type}
  `{Spec.Machine.RiscvMachine p t}
   : t -> list byte -> p unit :=
  fun memAddr value =>
    forM_ (zeroToExclusive_machineInt (len value)) (fun i =>
             Bind (Spec.VirtualMemory.translate Spec.Machine.Store 1 (memAddr +
                                                 Utility.Utility.fromImm i)) (fun addr =>
                     (Spec.Machine.storeByte Spec.Machine.Execute addr ((get value i))))).

Definition testVectorBit : list byte -> Z -> bool :=
  fun vregValue posn =>
    if (Z.eqb (Utility.Utility.bitSlice (get vregValue (div posn 8)) (rem posn 8)
                                        (rem posn 8 + 1)) 0) then false else true.

Definition execute {p : Type -> Type} {t : Type} `{Spec.Machine.RiscvMachine p
                                                                             t}
   : Spec.Decode.InstructionV -> p unit :=
  fun arg_0__ =>
    match arg_0__ with
    | Spec.Decode.Vsetvli rd rs1 vtypei =>
        Bind (Spec.Machine.getCSRField Spec.CSRField.VL) (fun old_vl =>
                if negb (Z.eqb rs1 0) : bool
                then Bind (Spec.Machine.getRegister rs1) (fun avl =>
                             executeVset false (Utility.Utility.regToInt64 avl) vtypei rd)
                else if negb (Z.eqb rd 0) : bool
                     then executeVset false (Utility.Utility.regToInt64
                                             (Utility.Utility.maxSigned : t)) vtypei rd
                     else executeVset true (Utility.Utility.regToInt64
                                            (Utility.Utility.maxSigned : t)) vtypei rd)
    | Spec.Decode.Vsetvl rd rs1 rs2 =>
        Bind (Spec.Machine.getRegister rs2) (fun vtypei =>
                Bind (Spec.Machine.getCSRField Spec.CSRField.VL) (fun old_vl =>
                        if negb (Z.eqb rs1 0) : bool
                        then Bind (Spec.Machine.getRegister rs1) (fun avl =>
                                     executeVset false (Utility.Utility.regToInt64 avl) (Utility.Utility.regToInt64
                                                                                         vtypei) rd)
                        else if negb (Z.eqb rd 0) : bool
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
                                                                let eltsPerVReg := div (vlenb * 8) (eew) in
                                                                Bind (forM_ (rangeNonNegZ vstart (vl - 1)) (fun i =>
                                                                               let realEltIdx := (rem i eltsPerVReg) in
                                                                               let realVd := vd + div i eltsPerVReg in
                                                                               Bind (Spec.Machine.getRegister rs1)
                                                                                    (fun baseMem =>
                                                                                       Bind (loadUntranslatedBytes
                                                                                             (baseMem +
                                                                                              Utility.Utility.fromImm (i
                                                                                                                       *
                                                                                                                       div
                                                                                                                       eew
                                                                                                                       8))
                                                                                             (div eew 8)) (fun mem =>
                                                                                               Bind (when (orb (Z.eqb vm
                                                                                                                      1)
                                                                                                               (testVectorBit
                                                                                                                vmask
                                                                                                                (i)))
                                                                                                          ((setVRegisterElement
                                                                                                            (Utility.Utility.fromImm
                                                                                                             ((div eew
                                                                                                                   8)))
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
                                                                                                                    ((div
                                                                                                                      eew
                                                                                                                      8)))
                                                                                                                   (Utility.Utility.fromImm
                                                                                                                    (realVd))
                                                                                                                   (Utility.Utility.fromImm
                                                                                                                    (realEltIdx))
                                                                                                                   (repeat
                                                                                                                    (div
                                                                                                                     eew
                                                                                                                     8)
                                                                                                                    yx)))
                                                                                                            (fun _ =>
                                                                                                               Spec.Machine.setCSRField
                                                                                                               Spec.CSRField.VStart
                                                                                                               i))))))
                                                                     (fun _ =>
                                                                        Bind (when (Z.eqb vta 1) (forM_ (rangeNonNegZ vl
                                                                                                                      (maxTail
                                                                                                                       -
                                                                                                                       1))
                                                                                                        (fun i =>
                                                                                                           let realEltIdx :=
                                                                                                             (rem i
                                                                                                                  eltsPerVReg) in
                                                                                                           let realVd :=
                                                                                                             vd +
                                                                                                             div i
                                                                                                                 eltsPerVReg in
                                                                                                           (setVRegisterElement
                                                                                                            (Utility.Utility.fromImm
                                                                                                             ((div eew
                                                                                                                   8)))
                                                                                                            (Utility.Utility.fromImm
                                                                                                             (realVd))
                                                                                                            (Utility.Utility.fromImm
                                                                                                             (realEltIdx))
                                                                                                            (repeat (div
                                                                                                                     eew
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
                                                                        let eltsPerVReg := div (vlenb * 8) (eew) in
                                                                        Bind (forM_ (rangeNonNegZ vstart (vl - 1))
                                                                                    (fun i =>
                                                                                       let realEltIdx :=
                                                                                         (rem i eltsPerVReg) in
                                                                                       let realVs2 :=
                                                                                         vs2 + div i eltsPerVReg in
                                                                                       let realVs1 :=
                                                                                         vs1 + div i eltsPerVReg in
                                                                                       let realVd :=
                                                                                         vd + div i eltsPerVReg in
                                                                                       Bind (getVRegisterElement
                                                                                             (Utility.Utility.fromImm
                                                                                              (div eew 8))
                                                                                             (Utility.Utility.fromImm
                                                                                              (realVs1))
                                                                                             (Utility.Utility.fromImm
                                                                                              (realEltIdx)))
                                                                                            (fun vs1value =>
                                                                                               Bind (getVRegisterElement
                                                                                                     (Utility.Utility.fromImm
                                                                                                      (div eew 8))
                                                                                                     (Utility.Utility.fromImm
                                                                                                      (realVs2))
                                                                                                     (Utility.Utility.fromImm
                                                                                                      (realEltIdx)))
                                                                                                    (fun vs2value =>
                                                                                                       let vs2Element :=
                                                                                                         ((Utility.Utility.combineBytes : list
                                                                                                           byte ->
                                                                                                           Z)
                                                                                                          (Coq.Lists.List.map
                                                                                                           int8_toWord8
                                                                                                           vs2value)) in
                                                                                                       let vs1Element :=
                                                                                                         ((Utility.Utility.combineBytes : list
                                                                                                           byte ->
                                                                                                           Z)
                                                                                                          (Coq.Lists.List.map
                                                                                                           int8_toWord8
                                                                                                           vs1value)) in
                                                                                                       let vdElement :=
                                                                                                         vs1Element +
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
                                                                                                                  (div
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
                                                                                                                     ((div
                                                                                                                       eew
                                                                                                                       8)))
                                                                                                                    (Utility.Utility.fromImm
                                                                                                                     (realVd))
                                                                                                                    (Utility.Utility.fromImm
                                                                                                                     (realEltIdx))
                                                                                                                    (repeat
                                                                                                                     (div
                                                                                                                      eew
                                                                                                                      8)
                                                                                                                     yx)))
                                                                                                                  (fun _ =>
                                                                                                                     Spec.Machine.setCSRField
                                                                                                                     Spec.CSRField.VStart
                                                                                                                     i)))))))
                                                                             (fun _ =>
                                                                                Bind (when (Z.eqb vta 1) (forM_
                                                                                            (rangeNonNegZ vl (maxTail -
                                                                                                           1)) (fun i =>
                                                                                               let realEltIdx :=
                                                                                                 (rem i eltsPerVReg) in
                                                                                               let realVd :=
                                                                                                 vd +
                                                                                                 div i eltsPerVReg in
                                                                                               setVRegisterElement
                                                                                               (Utility.Utility.fromImm
                                                                                                ((div eew 8)))
                                                                                               (Utility.Utility.fromImm
                                                                                                (realVd))
                                                                                               (Utility.Utility.fromImm
                                                                                                (realEltIdx)) (repeat
                                                                                                               (div eew
                                                                                                                    8)
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
                                                                let eltsPerVReg := div (vlenb * 8) (eew) in
                                                                Bind (forM_ (rangeNonNegZ vstart (vl - 1)) (fun i =>
                                                                               let realEltIdx := (rem i eltsPerVReg) in
                                                                               let realVd := vd + div i eltsPerVReg in
                                                                               Bind (Spec.Machine.getRegister rs1)
                                                                                    (fun baseMem =>
                                                                                       Bind (getVRegisterElement
                                                                                             (Utility.Utility.fromImm
                                                                                              ((div eew 8)))
                                                                                             (Utility.Utility.fromImm
                                                                                              (realVd))
                                                                                             (Utility.Utility.fromImm
                                                                                              (realEltIdx)))
                                                                                            (fun value =>
                                                                                               Bind
                                                                                               (storeUntranslatedBytes
                                                                                                (baseMem +
                                                                                                 Utility.Utility.fromImm
                                                                                                 (i * div eew 8)) value)
                                                                                               (fun _ =>
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
                           (Z.eqb (rem (vd) numFields) 0)) (forM_ (rangeNonNegZ 0 (numFields - 1))
                                                                  (fun i =>
                                                                     Bind (Spec.Machine.getRegister rs1) (fun baseMem =>
                                                                             Bind (loadUntranslatedBytes (baseMem +
                                                                                                          Utility.Utility.fromImm
                                                                                                          (vlenb * i))
                                                                                                         (vlenb))
                                                                                  (fun mem =>
                                                                                     Spec.Machine.setVRegister (vd + i)
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
                           (Z.eqb (rem (vs3) numFields) 0)) (forM_ (rangeNonNegZ 0 (numFields - 1))
                                                                   (fun i =>
                                                                      Bind (Spec.Machine.getRegister rs1)
                                                                           (fun baseMem =>
                                                                              Bind (Spec.Machine.getVRegister (vs3 + i))
                                                                                   (fun value =>
                                                                                      storeUntranslatedBytes (baseMem +
                                                                                                              Utility.Utility.fromImm
                                                                                                              (vlenb *
                                                                                                               i))
                                                                                      value)))))
    | _ => GHC.Err.patternFailure
    end.

(* External variables:
     Bind None Return Some Type Z Z.eqb Z.pow andb bool byte cons div else false forM
     forM_ forallb from get if int8_toWord8 len list negate negb nil op_zm__ op_zp__
     op_zt__ option orb rangeNonNegZ rem repeat then true unit unless upto when
     word8_toInt8 yx Coq.Init.Datatypes.app Coq.Lists.List.map GHC.Base.op_zeze__
     GHC.Base.op_zgze__ GHC.Base.op_zl__ GHC.Base.op_zlze__ GHC.Err.patternFailure
     GHC.Num.fromInteger Spec.CSRField.VIll Spec.CSRField.VL Spec.CSRField.VLMul
     Spec.CSRField.VLenB Spec.CSRField.VMA Spec.CSRField.VSEW Spec.CSRField.VStart
     Spec.CSRField.VTA Spec.Decode.InstructionV Spec.Decode.Register
     Spec.Decode.VRegister Spec.Decode.Vaddvv Spec.Decode.Vle Spec.Decode.Vlr
     Spec.Decode.Vse Spec.Decode.Vsetivli Spec.Decode.Vsetvl Spec.Decode.Vsetvli
     Spec.Decode.Vsr Spec.Machine.Execute Spec.Machine.Load Spec.Machine.RiscvMachine
     Spec.Machine.Store Spec.Machine.getCSRField Spec.Machine.getRegister
     Spec.Machine.getVRegister Spec.Machine.loadByte Spec.Machine.raiseException
     Spec.Machine.setCSRField Spec.Machine.setRegister Spec.Machine.setVRegister
     Spec.Machine.storeByte Spec.VirtualMemory.translate Utility.Utility.MachineWidth
     Utility.Utility.bitSlice Utility.Utility.combineBytes Utility.Utility.fromImm
     Utility.Utility.maxSigned Utility.Utility.regToInt64 Utility.Utility.splitBytes
     Z.eqb
*)
