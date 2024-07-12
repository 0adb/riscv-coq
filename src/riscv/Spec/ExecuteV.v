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
Local Open Scope Z.
Require Import riscv.Utility.Utility.
Local Open Scope alu_scope.

(* Converted imports: *)

Require Control.Monad.
Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Import Coq.ZArith.BinInt.
Require Data.Bits.
Require Data.Foldable.
Require Data.Maybe.
Require Data.Traversable.
Require Debug.Trace.
Require GHC.Base.
Require GHC.Enum.
Require GHC.Err.
Require GHC.Int.
Require GHC.List.
Require GHC.Maybe.
Require GHC.Num.
Require GHC.Real.
Require GHC.Show.
Require Import Monads.
Require Spec.CSRField.
Require Spec.Decode.
Require Spec.Machine.
Require Spec.VirtualMemory.
Require Import Utility.
Require Utility.Utility.
Import GHC.Base.Notations.
Import GHC.List.Notations.
Import GHC.Num.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition take_machineInt {t : Type}
   : Utility.Utility.MachineInt -> list t -> list t :=
  fun i l => GHC.List.take (GHC.Real.fromIntegral i) l.

Definition drop_machineInt {t : Type}
   : Utility.Utility.MachineInt -> list t -> list t :=
  fun i l => GHC.List.drop (GHC.Real.fromIntegral i) l.

Definition replicate_machineInt {t : Type}
   : Utility.Utility.MachineInt -> t -> list t :=
  fun c v => GHC.List.replicate (GHC.Real.fromIntegral c) v.

Definition zeroToExclusive_machineInt {t : Type} `{Utility.Utility.MachineWidth
  t}
   : Utility.Utility.MachineInt -> list t :=
  fun max =>
    Coq.Lists.List.map (Utility.Utility.fromImm) (GHC.Enum.enumFromTo (ZToReg 0)
                                                                      (max - ZToReg 1)).

Definition length_machineInt {t : Type}
   : list t -> Utility.Utility.MachineInt :=
  fun l => (GHC.Real.fromIntegral (Data.Foldable.length l)).

Definition maybeIndex_machineInt {t : Type}
   : list t -> Utility.Utility.MachineInt -> GHC.Maybe.Maybe t :=
  fun l idx =>
    if (length_machineInt l > idx) : bool
    then (GHC.Maybe.Just (l GHC.List.!! (GHC.Real.fromIntegral idx)))
    else GHC.Maybe.Nothing.

Definition testBit_machineInt {a : Type} `{Data.Bits.Bits a}
   : a -> Utility.Utility.MachineInt -> bool :=
  fun b idx => Data.Bits.testBit b (GHC.Real.fromIntegral idx).

Definition translateSEW {t : Type} `{Utility.Utility.MachineWidth t}
   : t -> GHC.Maybe.Maybe Utility.Utility.MachineInt :=
  fun arg_0__ =>
    let 'num_1__ := arg_0__ in
    if num_1__ GHC.Base.== #0 : bool then GHC.Maybe.Just (ZToReg 3) else
    let 'num_2__ := arg_0__ in
    if num_2__ GHC.Base.== #1 : bool then GHC.Maybe.Just (ZToReg 4) else
    let 'num_3__ := arg_0__ in
    if num_3__ GHC.Base.== #2 : bool then GHC.Maybe.Just (ZToReg 5) else
    let 'num_4__ := arg_0__ in
    if num_4__ GHC.Base.== #3 : bool then GHC.Maybe.Just (ZToReg 6) else
    GHC.Maybe.Nothing.

Definition translateLMUL {t : Type} `{Utility.Utility.MachineWidth t}
   : t -> GHC.Maybe.Maybe Utility.Utility.MachineInt :=
  fun arg_0__ =>
    let 'num_1__ := arg_0__ in
    if num_1__ GHC.Base.== #5 : bool then GHC.Maybe.Just (negate (ZToReg 3)) else
    let 'num_2__ := arg_0__ in
    if num_2__ GHC.Base.== #6 : bool then GHC.Maybe.Just (negate (ZToReg 2)) else
    let 'num_3__ := arg_0__ in
    if num_3__ GHC.Base.== #7 : bool then GHC.Maybe.Just (negate (ZToReg 1)) else
    let 'num_4__ := arg_0__ in
    if num_4__ GHC.Base.== #0 : bool then GHC.Maybe.Just (ZToReg 0) else
    let 'num_5__ := arg_0__ in
    if num_5__ GHC.Base.== #1 : bool then GHC.Maybe.Just (ZToReg 1) else
    let 'num_6__ := arg_0__ in
    if num_6__ GHC.Base.== #2 : bool then GHC.Maybe.Just (ZToReg 2) else
    let 'num_7__ := arg_0__ in
    if num_7__ GHC.Base.== #3 : bool then GHC.Maybe.Just (ZToReg 3) else
    GHC.Maybe.Nothing.

Definition translateWidth {t : Type} `{Utility.Utility.MachineWidth t}
   : t -> GHC.Maybe.Maybe Utility.Utility.MachineInt :=
  fun arg_0__ =>
    let 'num_1__ := arg_0__ in
    if num_1__ GHC.Base.== #0 : bool then GHC.Maybe.Just (ZToReg 8) else
    let 'num_2__ := arg_0__ in
    if num_2__ GHC.Base.== #5 : bool then GHC.Maybe.Just (ZToReg 16) else
    let 'num_3__ := arg_0__ in
    if num_3__ GHC.Base.== #6 : bool then GHC.Maybe.Just (ZToReg 32) else
    let 'num_4__ := arg_0__ in
    if num_4__ GHC.Base.== #7 : bool then GHC.Maybe.Just (ZToReg 64) else
    GHC.Maybe.Nothing.

Definition translateNumFields
   : Utility.Utility.MachineInt -> GHC.Maybe.Maybe Utility.Utility.MachineInt :=
  fun arg_0__ =>
    let 'num_1__ := arg_0__ in
    if num_1__ GHC.Base.== #0 : bool then GHC.Maybe.Just (ZToReg 1) else
    let 'num_2__ := arg_0__ in
    if num_2__ GHC.Base.== #1 : bool then GHC.Maybe.Just (ZToReg 2) else
    let 'num_3__ := arg_0__ in
    if num_3__ GHC.Base.== #2 : bool then GHC.Maybe.Just (ZToReg 3) else
    let 'num_4__ := arg_0__ in
    if num_4__ GHC.Base.== #3 : bool then GHC.Maybe.Just (ZToReg 4) else
    let 'num_5__ := arg_0__ in
    if num_5__ GHC.Base.== #4 : bool then GHC.Maybe.Just (ZToReg 5) else
    let 'num_6__ := arg_0__ in
    if num_6__ GHC.Base.== #5 : bool then GHC.Maybe.Just (ZToReg 6) else
    let 'num_7__ := arg_0__ in
    if num_7__ GHC.Base.== #6 : bool then GHC.Maybe.Just (ZToReg 7) else
    let 'num_8__ := arg_0__ in
    if num_8__ GHC.Base.== #7 : bool then GHC.Maybe.Just (ZToReg 8) else
    GHC.Maybe.Nothing.

Definition legalSEW {t : Type} `{Utility.Utility.MachineWidth t}
   : t -> t -> t -> bool :=
  fun vsew vlmul vlenb =>
    Data.Maybe.fromMaybe false (Bind (translateSEW vsew) (fun pow2SEW =>
                                        Bind (translateLMUL vlmul) (fun pow2LMUL =>
                                                Return (Z.pow (ZToReg 2) pow2SEW <=
                                                        Z.pow (ZToReg 2) pow2LMUL * vlenb * ZToReg 8)))).

Definition consistentRatio {t : Type} `{Utility.Utility.MachineWidth t}
   : t -> t -> t -> t -> bool :=
  fun vlmul vsew vlmul' vsew' =>
    Data.Maybe.fromMaybe false (Bind (translateSEW vsew) (fun pow2SEW =>
                                        Bind (translateLMUL vlmul) (fun pow2LMUL =>
                                                Bind (translateSEW vsew') (fun pow2SEW' =>
                                                        Bind (translateLMUL vlmul') (fun pow2LMUL' =>
                                                                Return (reg_eqb (pow2SEW - pow2LMUL) (pow2SEW' -
                                                                                 pow2LMUL'))))))).

Definition computeVLMAX {t : Type} `{Utility.Utility.MachineWidth t}
   : t -> t -> t -> t :=
  fun vlmul vsew vlenb =>
    Data.Maybe.fromMaybe (ZToReg 0) (Bind (translateSEW vsew) (fun pow2SEW =>
                                             Bind (translateLMUL vlmul) (fun pow2LMUL =>
                                                     Return (ZToReg 8 * vlenb *
                                                             Z.pow (ZToReg 2) (pow2LMUL - pow2SEW))))).

Definition computeMaxTail {t : Type} `{Utility.Utility.MachineWidth t}
   : t -> t -> t -> t :=
  fun vlmul vlenb vsew =>
    Data.Maybe.fromMaybe (ZToReg 0) (Bind (translateSEW vsew) (fun pow2SEW =>
                                             Bind (translateLMUL vlmul) (fun pow2LMUL =>
                                                     let tail :=
                                                       ZToReg 8 * vlenb *
                                                       Z.pow (ZToReg 2) ((if pow2LMUL < ZToReg 0 : bool
                                                               then ZToReg 0
                                                               else pow2LMUL) -
                                                              pow2SEW) in
                                                     if tail >= ZToReg 1 : bool
                                                     then Return tail
                                                     else Return (ZToReg 0)))).

Definition executeVset {p : Type -> Type} {t : Type} `{Spec.Machine.RiscvMachine
  p t}
   : bool -> t -> t -> Spec.Decode.Register -> p unit :=
  fun noRatioCheck avl vtypei rd =>
    let vma := (Utility.Utility.bitSlice vtypei (ZToReg 7) (ZToReg 8)) in
    let vta := (Utility.Utility.bitSlice vtypei (ZToReg 6) (ZToReg 7)) in
    let vsew := (Utility.Utility.bitSlice vtypei (ZToReg 3) (ZToReg 6)) in
    let vlmul := (Utility.Utility.bitSlice vtypei (ZToReg 0) (ZToReg 3)) in
    Bind (Spec.Machine.getCSRField Spec.CSRField.VLMul) (fun vlmul_old =>
            Bind (Spec.Machine.getCSRField Spec.CSRField.VSEW) (fun vsew_old =>
                    Bind (Spec.Machine.getCSRField Spec.CSRField.VLenB) (fun vlenb =>
                            Bind (Spec.Machine.setCSRField Spec.CSRField.VLMul vlmul) (fun _ =>
                                    Bind (Spec.Machine.setCSRField Spec.CSRField.VSEW vsew) (fun _ =>
                                            Bind (Spec.Machine.setCSRField Spec.CSRField.VMA vma) (fun _ =>
                                                    Bind (Spec.Machine.setCSRField Spec.CSRField.VTA vta) (fun _ =>
                                                            let vlmax :=
                                                              computeVLMAX vlmul vsew (Utility.Utility.fromImm vlenb) in
                                                            let vl := (if avl <= vlmax : bool then (avl) else vlmax) in
                                                            let vill :=
                                                              (if (andb (legalSEW vsew vlmul (Utility.Utility.fromImm
                                                                                              vlenb)) (orb noRatioCheck
                                                                                                           (consistentRatio
                                                                                                            (Utility.Utility.fromImm
                                                                                                             vlmul_old)
                                                                                                            (Utility.Utility.fromImm
                                                                                                             vsew_old)
                                                                                                            vlmul
                                                                                                            vsew))) : bool
                                                               then ZToReg 0
                                                               else ZToReg 1) in
                                                            Bind (Spec.Machine.setCSRField Spec.CSRField.VL vl)
                                                                 (fun _ =>
                                                                    Bind (Spec.Machine.setCSRField Spec.CSRField.VStart
                                                                                                   (ZToReg 0)) (fun _ =>
                                                                            Bind (Spec.Machine.setCSRField
                                                                                  Spec.CSRField.VIll vill) (fun _ =>
                                                                                    Control.Monad.unless (reg_eqb rd
                                                                                                                  (ZToReg
                                                                                                                   0))
                                                                                                         (Spec.Machine.setRegister
                                                                                                          rd
                                                                                                          vl))))))))))).

Definition getVRegisterElement {p : Type -> Type} {t : Type}
  `{Spec.Machine.RiscvMachine p t}
   : Utility.Utility.MachineInt ->
     Spec.Decode.VRegister -> Utility.Utility.MachineInt -> p (list GHC.Int.Int8) :=
  fun eew baseReg eltIndex =>
    if (Data.Foldable.and (cons (eew /= ZToReg 1) (cons (eew /= ZToReg 2) (cons (eew
                                                                                 /=
                                                                                 ZToReg 4) (cons (eew /= ZToReg 8)
                                                                                                 nil))))) : bool
    then Spec.Machine.raiseException (ZToReg 0) (ZToReg 2)
    else Bind (Spec.Machine.getCSRField Spec.CSRField.VLenB) (fun vlenb =>
                 Bind (Spec.Machine.getVRegister baseReg) (fun vregValue =>
                         let value :=
                           take_machineInt (eew) (drop_machineInt ((eltIndex * eew)) vregValue) in
                         if reg_eqb (length_machineInt value) eew : bool
                         then Debug.Trace.trace (Coq.Init.Datatypes.app (GHC.Base.hs_string__
                                                                         "value loaded from vregister: ")
                                                                        (Coq.Init.Datatypes.app (GHC.Show.show value)
                                                                                                (Coq.Init.Datatypes.app
                                                                                                 (GHC.Base.hs_string__
                                                                                                  "at vregister ")
                                                                                                 (Coq.Init.Datatypes.app
                                                                                                  (GHC.Show.show
                                                                                                   baseReg)
                                                                                                  (Coq.Init.Datatypes.app
                                                                                                   (GHC.Base.hs_string__
                                                                                                    " elt idx ")
                                                                                                   (GHC.Show.show
                                                                                                    eltIndex))))))
                              (Return value)
                         else Spec.Machine.raiseException (ZToReg 0) (ZToReg 2))).

Definition setVRegisterElement {p : Type -> Type} {t : Type}
  `{Spec.Machine.RiscvMachine p t}
   : Utility.Utility.MachineInt ->
     Spec.Decode.VRegister ->
     Utility.Utility.MachineInt -> list GHC.Int.Int8 -> p unit :=
  fun eew baseReg eltIndex value =>
    if (Data.Foldable.and (cons (eew /= ZToReg 1) (cons (eew /= ZToReg 2) (cons (eew
                                                                                 /=
                                                                                 ZToReg 4) (cons (eew /= ZToReg 8)
                                                                                                 nil))))) : bool
    then Spec.Machine.raiseException (ZToReg 0) (ZToReg 2)
    else Bind (Spec.Machine.getCSRField Spec.CSRField.VLenB) (fun vlenb =>
                 Bind (Spec.Machine.getVRegister baseReg) (fun vregValue =>
                         let newVregValue :=
                           Coq.Init.Datatypes.app (take_machineInt ((eltIndex * eew)) vregValue)
                                                  (Coq.Init.Datatypes.app (value) (drop_machineInt (((eltIndex +
                                                                                                      ZToReg 1) *
                                                                                                     eew))
                                                                           vregValue)) in
                         if reg_eqb (Data.Foldable.length newVregValue) (Data.Foldable.length
                                     vregValue) : bool
                         then Debug.Trace.trace (Coq.Init.Datatypes.app (GHC.Base.hs_string__
                                                                         "value stored to vregister: ")
                                                                        (Coq.Init.Datatypes.app (GHC.Show.show
                                                                                                 newVregValue)
                                                                                                (Coq.Init.Datatypes.app
                                                                                                 (GHC.Base.hs_string__
                                                                                                  " at register idx ")
                                                                                                 (GHC.Show.show
                                                                                                  baseReg))))
                              (Spec.Machine.setVRegister baseReg newVregValue)
                         else Spec.Machine.raiseException (ZToReg 0) (ZToReg 2))).

Definition loadUntranslatedBytes {p : Type -> Type} {t : Type}
  `{Spec.Machine.RiscvMachine p t}
   : t -> Utility.Utility.MachineInt -> p (list GHC.Int.Int8) :=
  fun memAddr numBytes =>
    Data.Traversable.forM (zeroToExclusive_machineInt numBytes) (fun i =>
                                                                   Bind (Spec.VirtualMemory.translate Spec.Machine.Load
                                                                                                      (ZToReg 1)
                                                                                                      (memAddr +
                                                                                                       Utility.Utility.fromImm
                                                                                                       i)) (fun addr =>
                                                                           Debug.Trace.trace (Coq.Init.Datatypes.app
                                                                                              (GHC.Base.hs_string__
                                                                                               "loading from address")
                                                                                              (GHC.Show.show
                                                                                               (GHC.Real.fromIntegral
                                                                                                addr)))
                                                                           (Spec.Machine.loadByte Spec.Machine.Execute
                                                                                                  addr))).

Definition storeUntranslatedBytes {p : Type -> Type} {t : Type}
  `{Spec.Machine.RiscvMachine p t}
   : t -> list GHC.Int.Int8 -> p unit :=
  fun memAddr value =>
    Data.Foldable.forM_ (zeroToExclusive_machineInt (length_machineInt value))
    (fun i =>
       Bind (Spec.VirtualMemory.translate Spec.Machine.Store (ZToReg 1) (memAddr +
                                           Utility.Utility.fromImm i)) (fun addr =>
               Debug.Trace.trace (Coq.Init.Datatypes.app (GHC.Base.hs_string__
                                                          "storing at address ") (Coq.Init.Datatypes.app (GHC.Show.show
                                                                                                          (GHC.Real.fromIntegral
                                                                                                           addr))
                                                                                                         (Coq.Init.Datatypes.app
                                                                                                          (GHC.Base.hs_string__
                                                                                                           " the value ")
                                                                                                          (Coq.Init.Datatypes.app
                                                                                                           (GHC.Show.show
                                                                                                            value)
                                                                                                           (Coq.Init.Datatypes.app
                                                                                                            (GHC.Base.hs_string__
                                                                                                             " and index ")
                                                                                                            (GHC.Show.show
                                                                                                             i))))))
               (Spec.Machine.storeByte Spec.Machine.Execute addr (Data.Maybe.fromMaybe (ZToReg
                                                                                        0) (maybeIndex_machineInt value
                                                                                            i))))).

Definition testVectorBit
   : list GHC.Int.Int8 -> Utility.Utility.MachineInt -> bool :=
  fun vregValue posn =>
    testBit_machineInt (Data.Maybe.fromMaybe (ZToReg 0) (maybeIndex_machineInt
                                                         vregValue (GHC.Real.div posn (ZToReg 8)))) ((rem posn (ZToReg
                                                                                                           8))).

Definition execute {p : Type -> Type} {t : Type} `{Spec.Machine.RiscvMachine p
                                                                             t}
   : Spec.Decode.InstructionV -> p unit :=
  fun arg_0__ =>
    match arg_0__ with
    | Spec.Decode.Vsetvli rd rs1 vtypei =>
        Bind (Spec.Machine.getCSRField Spec.CSRField.VL) (fun old_vl =>
                if rs1 /= ZToReg 0 : bool
                then Bind (Spec.Machine.getRegister rs1) (fun avl =>
                             executeVset false avl (Utility.Utility.fromImm vtypei) rd)
                else if rd /= ZToReg 0 : bool
                     then executeVset false (Utility.Utility.fromImm
                                             (GHC.Enum.maxBound : Utility.Utility.MachineInt)) (Utility.Utility.fromImm
                                                                                                vtypei) rd
                     else executeVset true (Utility.Utility.fromImm old_vl) (Utility.Utility.fromImm
                                                                             vtypei) rd)
    | Spec.Decode.Vsetvl rd rs1 rs2 =>
        Bind (Spec.Machine.getRegister rs2) (fun vtypei =>
                Bind (Spec.Machine.getCSRField Spec.CSRField.VL) (fun old_vl =>
                        if rs1 /= ZToReg 0 : bool
                        then Bind (Spec.Machine.getRegister rs1) (fun avl =>
                                     executeVset false avl vtypei rd)
                        else if rd /= ZToReg 0 : bool
                             then executeVset false (Utility.Utility.fromImm
                                                     (GHC.Enum.maxBound : Utility.Utility.MachineInt)) vtypei rd
                             else executeVset true (Utility.Utility.fromImm old_vl) vtypei rd))
    | Spec.Decode.Vsetivli rd uimm vtypei =>
        executeVset false (Utility.Utility.fromImm uimm) (Utility.Utility.fromImm
                                                          vtypei) rd
    | Spec.Decode.Vle width vd rs1 vm =>
        Bind (Spec.Machine.getCSRField Spec.CSRField.VStart) (fun vstart =>
                Bind (Spec.Machine.getCSRField Spec.CSRField.VLMul) (fun vlmul =>
                        Bind (Spec.Machine.getCSRField Spec.CSRField.VLenB) (fun vlenb =>
                                Bind (Spec.Machine.getCSRField Spec.CSRField.VL) (fun vl =>
                                        Bind (Spec.Machine.getCSRField Spec.CSRField.VMA) (fun vma =>
                                                Bind (Spec.Machine.getCSRField Spec.CSRField.VTA) (fun vta =>
                                                        Bind (Spec.Machine.getVRegister (ZToReg 0)) (fun vmask =>
                                                                let eew :=
                                                                  Data.Maybe.fromMaybe (ZToReg 8) (translateWidth
                                                                                                   width) in
                                                                let maxTail := computeMaxTail vlmul vlenb (eew) in
                                                                let eltsPerVReg :=
                                                                  GHC.Real.div (vlenb * ZToReg 8) (eew) in
                                                                Bind (Data.Foldable.forM_ (GHC.Enum.enumFromTo vstart
                                                                                                               (vl -
                                                                                                                ZToReg
                                                                                                                1))
                                                                                          (fun i =>
                                                                                             let realEltIdx :=
                                                                                               (rem i eltsPerVReg) in
                                                                                             let realVd :=
                                                                                               vd +
                                                                                               GHC.Real.div i
                                                                                                            eltsPerVReg in
                                                                                             Bind
                                                                                             (Spec.Machine.getRegister
                                                                                              rs1) (fun baseMem =>
                                                                                                Bind
                                                                                                (loadUntranslatedBytes
                                                                                                 (baseMem +
                                                                                                  Utility.Utility.fromImm
                                                                                                  (i *
                                                                                                   GHC.Real.div eew
                                                                                                                (ZToReg
                                                                                                                 8)))
                                                                                                 (GHC.Real.div eew
                                                                                                               (ZToReg
                                                                                                                8)))
                                                                                                (fun mem =>
                                                                                                   Bind (when (orb
                                                                                                               (reg_eqb
                                                                                                                vm
                                                                                                                (ZToReg
                                                                                                                 1))
                                                                                                               (testVectorBit
                                                                                                                vmask
                                                                                                                (i)))
                                                                                                              (setVRegisterElement
                                                                                                               (Utility.Utility.fromImm
                                                                                                                ((GHC.Real.div
                                                                                                                  eew
                                                                                                                  (ZToReg
                                                                                                                   8))))
                                                                                                               (Utility.Utility.fromImm
                                                                                                                (realVd))
                                                                                                               (Utility.Utility.fromImm
                                                                                                                (realEltIdx))
                                                                                                               mem))
                                                                                                        (fun _ =>
                                                                                                           Bind (when
                                                                                                                 (andb
                                                                                                                  (reg_eqb
                                                                                                                   vm
                                                                                                                   (ZToReg
                                                                                                                    0))
                                                                                                                  (andb
                                                                                                                   (negb
                                                                                                                    (testVectorBit
                                                                                                                     vmask
                                                                                                                     (i)))
                                                                                                                   (reg_eqb
                                                                                                                    vma
                                                                                                                    (ZToReg
                                                                                                                     1))))
                                                                                                                 (setVRegisterElement
                                                                                                                  (Utility.Utility.fromImm
                                                                                                                   ((GHC.Real.div
                                                                                                                     eew
                                                                                                                     (ZToReg
                                                                                                                      8))))
                                                                                                                  (Utility.Utility.fromImm
                                                                                                                   (realVd))
                                                                                                                  (Utility.Utility.fromImm
                                                                                                                   (realEltIdx))
                                                                                                                  (replicate_machineInt
                                                                                                                   (GHC.Real.div
                                                                                                                    eew
                                                                                                                    (ZToReg
                                                                                                                     8))
                                                                                                                   (lnot
                                                                                                                    (Data.Bits.zeroBits : GHC.Int.Int8)))))
                                                                                                                (fun _ =>
                                                                                                                   Spec.Machine.setCSRField
                                                                                                                   Spec.CSRField.VStart
                                                                                                                   i))))))
                                                                     (fun _ =>
                                                                        Bind (when (reg_eqb vta (ZToReg 1))
                                                                                   (Data.Foldable.forM_
                                                                                    (GHC.Enum.enumFromTo vl ((maxTail -
                                                                                                           ZToReg 1)))
                                                                                    (fun i =>
                                                                                       let realEltIdx :=
                                                                                         (rem i eltsPerVReg) in
                                                                                       let realVd :=
                                                                                         vd +
                                                                                         GHC.Real.div i eltsPerVReg in
                                                                                       (setVRegisterElement
                                                                                        (Utility.Utility.fromImm
                                                                                         ((GHC.Real.div eew (ZToReg
                                                                                                         8))))
                                                                                        (Utility.Utility.fromImm
                                                                                         (realVd))
                                                                                        (Utility.Utility.fromImm
                                                                                         (realEltIdx))
                                                                                        (replicate_machineInt
                                                                                         (GHC.Real.div eew (ZToReg 8))
                                                                                         (lnot
                                                                                          (Data.Bits.zeroBits : GHC.Int.Int8)))))))
                                                                             (fun _ =>
                                                                                Spec.Machine.setCSRField
                                                                                Spec.CSRField.VStart (ZToReg 0))))))))))
    | Spec.Decode.Vse width vd rs1 vm =>
        Bind (Spec.Machine.getCSRField Spec.CSRField.VStart) (fun vstart =>
                Bind (Spec.Machine.getCSRField Spec.CSRField.VLMul) (fun vlmul =>
                        Bind (Spec.Machine.getCSRField Spec.CSRField.VLenB) (fun vlenb =>
                                Bind (Spec.Machine.getCSRField Spec.CSRField.VL) (fun vl =>
                                        Bind (Spec.Machine.getCSRField Spec.CSRField.VMA) (fun vma =>
                                                Bind (Spec.Machine.getCSRField Spec.CSRField.VTA) (fun vta =>
                                                        Bind (Spec.Machine.getVRegister (ZToReg 0)) (fun vmask =>
                                                                let eew :=
                                                                  Data.Maybe.fromMaybe (ZToReg 8) (translateWidth
                                                                                                   width) in
                                                                let maxTail := computeMaxTail vlmul vlenb (eew) in
                                                                let eltsPerVReg :=
                                                                  GHC.Real.div (vlenb * ZToReg 8) (eew) in
                                                                Bind (Data.Foldable.forM_ (GHC.Enum.enumFromTo vstart
                                                                                                               (vl -
                                                                                                                ZToReg
                                                                                                                1))
                                                                                          (fun i =>
                                                                                             let realEltIdx :=
                                                                                               (rem i eltsPerVReg) in
                                                                                             let realVd :=
                                                                                               vd +
                                                                                               GHC.Real.div i
                                                                                                            eltsPerVReg in
                                                                                             Bind
                                                                                             (Spec.Machine.getRegister
                                                                                              rs1) (fun baseMem =>
                                                                                                Bind
                                                                                                (getVRegisterElement
                                                                                                 (Utility.Utility.fromImm
                                                                                                  ((GHC.Real.div eew
                                                                                                                 (ZToReg
                                                                                                                  8))))
                                                                                                 (Utility.Utility.fromImm
                                                                                                  (realVd))
                                                                                                 (Utility.Utility.fromImm
                                                                                                  (realEltIdx)))
                                                                                                (fun value =>
                                                                                                   Bind
                                                                                                   (storeUntranslatedBytes
                                                                                                    (baseMem +
                                                                                                     Utility.Utility.fromImm
                                                                                                     (i *
                                                                                                      GHC.Real.div eew
                                                                                                                   (ZToReg
                                                                                                                    8)))
                                                                                                    value) (fun _ =>
                                                                                                      Spec.Machine.setCSRField
                                                                                                      Spec.CSRField.VStart
                                                                                                      i))))) (fun _ =>
                                                                        Spec.Machine.setCSRField Spec.CSRField.VStart
                                                                                                 (ZToReg 0)))))))))
    | Spec.Decode.Vlr vd rs1 nf =>
        let numFields := Data.Maybe.fromMaybe (ZToReg 9) (translateNumFields nf) in
        Bind (Spec.Machine.getCSRField Spec.CSRField.VLenB) (fun vlenb =>
                when (andb (orb (reg_eqb numFields (ZToReg 1)) (orb (reg_eqb numFields (ZToReg
                                                                              2)) (orb (reg_eqb numFields (ZToReg 4))
                                                                                       (reg_eqb numFields (ZToReg 8)))))
                           (reg_eqb (rem vd numFields) (ZToReg 0))) (Data.Foldable.forM_
                                                                     (GHC.Enum.enumFromTo (ZToReg 0) (numFields -
                                                                                           ZToReg 1)) (fun i =>
                                                                                                         Bind
                                                                                                         (Spec.Machine.getRegister
                                                                                                          rs1)
                                                                                                         (fun baseMem =>
                                                                                                            Bind
                                                                                                            (loadUntranslatedBytes
                                                                                                             (baseMem +
                                                                                                              Utility.Utility.fromImm
                                                                                                              (vlenb *
                                                                                                               i))
                                                                                                             (vlenb))
                                                                                                            (fun mem =>
                                                                                                               Debug.Trace.trace
                                                                                                               (Coq.Init.Datatypes.app
                                                                                                                (GHC.Base.hs_string__
                                                                                                                 "setting vreg ")
                                                                                                                (Coq.Init.Datatypes.app
                                                                                                                 (GHC.Show.show
                                                                                                                  (vd +
                                                                                                                   i))
                                                                                                                 (Coq.Init.Datatypes.app
                                                                                                                  (GHC.Base.hs_string__
                                                                                                                   " with values ")
                                                                                                                  (GHC.Show.show
                                                                                                                   mem))))
                                                                                                               (Spec.Machine.setVRegister
                                                                                                                (vd + i)
                                                                                                                mem))))))
    | Spec.Decode.Vsr vs3 rs1 nf =>
        let numFields := Data.Maybe.fromMaybe (ZToReg 9) (translateNumFields nf) in
        Bind (Spec.Machine.getCSRField Spec.CSRField.VLenB) (fun vlenb =>
                when (andb (orb (reg_eqb numFields (ZToReg 1)) (orb (reg_eqb numFields (ZToReg
                                                                              2)) (orb (reg_eqb numFields (ZToReg 4))
                                                                                       (reg_eqb numFields (ZToReg 8)))))
                           (reg_eqb (rem vs3 numFields) (ZToReg 0))) (Data.Foldable.forM_
                                                                      (GHC.Enum.enumFromTo (ZToReg 0) (numFields -
                                                                                            ZToReg 1)) (fun i =>
                                                                                                          Bind
                                                                                                          (Spec.Machine.getRegister
                                                                                                           rs1)
                                                                                                          (fun baseMem =>
                                                                                                             Bind
                                                                                                             (Spec.Machine.getVRegister
                                                                                                              (vs3 + i))
                                                                                                             (fun value =>
                                                                                                                Debug.Trace.trace
                                                                                                                (Coq.Init.Datatypes.app
                                                                                                                 (GHC.Base.hs_string__
                                                                                                                  "getting vreg ")
                                                                                                                 (Coq.Init.Datatypes.app
                                                                                                                  (GHC.Show.show
                                                                                                                   (vs3
                                                                                                                    +
                                                                                                                    i))
                                                                                                                  (Coq.Init.Datatypes.app
                                                                                                                   (GHC.Base.hs_string__
                                                                                                                    " with values ")
                                                                                                                   (GHC.Show.show
                                                                                                                    value))))
                                                                                                                (storeUntranslatedBytes
                                                                                                                 (baseMem
                                                                                                                  +
                                                                                                                  Utility.Utility.fromImm
                                                                                                                  (vlenb
                                                                                                                   *
                                                                                                                   i))
                                                                                                                 value))))))
    | _ => GHC.Err.patternFailure
    end.

(* External variables:
     Bind Return Type Z.pow ZToReg andb bool cons false list lnot negate negb nil
     op_zg__ op_zgze__ op_zl__ op_zlze__ op_zm__ op_zp__ op_zsze__ op_zt__ orb
     reg_eqb rem true unit when Control.Monad.unless Coq.Init.Datatypes.app
     Coq.Lists.List.map Data.Bits.Bits Data.Bits.testBit Data.Bits.zeroBits
     Data.Foldable.and Data.Foldable.forM_ Data.Foldable.length Data.Maybe.fromMaybe
     Data.Traversable.forM Debug.Trace.trace GHC.Base.op_zeze__ GHC.Enum.enumFromTo
     GHC.Enum.maxBound GHC.Err.patternFailure GHC.Int.Int8 GHC.List.drop
     GHC.List.op_znzn__ GHC.List.replicate GHC.List.take GHC.Maybe.Just
     GHC.Maybe.Maybe GHC.Maybe.Nothing GHC.Num.fromInteger GHC.Real.div
     GHC.Real.fromIntegral GHC.Show.show Spec.CSRField.VIll Spec.CSRField.VL
     Spec.CSRField.VLMul Spec.CSRField.VLenB Spec.CSRField.VMA Spec.CSRField.VSEW
     Spec.CSRField.VStart Spec.CSRField.VTA Spec.Decode.InstructionV
     Spec.Decode.Register Spec.Decode.VRegister Spec.Decode.Vle Spec.Decode.Vlr
     Spec.Decode.Vse Spec.Decode.Vsetivli Spec.Decode.Vsetvl Spec.Decode.Vsetvli
     Spec.Decode.Vsr Spec.Machine.Execute Spec.Machine.Load Spec.Machine.RiscvMachine
     Spec.Machine.Store Spec.Machine.getCSRField Spec.Machine.getRegister
     Spec.Machine.getVRegister Spec.Machine.loadByte Spec.Machine.raiseException
     Spec.Machine.setCSRField Spec.Machine.setRegister Spec.Machine.setVRegister
     Spec.Machine.storeByte Spec.VirtualMemory.translate Utility.Utility.MachineInt
     Utility.Utility.MachineWidth Utility.Utility.bitSlice Utility.Utility.fromImm
*)
