Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import coqutil.Z.Lia.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.Encode.

Record InstructionSet': Set := {
  supports_64bit: bool;
  (* supports_I: bool; always true *)
  supports_M: bool;
  supports_A: bool;
  supports_F: bool;
  supports_V: bool
}.

Definition toInstructionSet(i: InstructionSet'): option InstructionSet :=
  match i.(supports_64bit), i.(supports_M), i.(supports_A), i.(supports_F), i.(supports_V) with
  | false, false, false, false, false => Some RV32I
  | false, false, false, true, false  => Some RV32IF
  | false, false, true , false, false => Some RV32IA
  | false, false, true , true, false  => Some RV32IAF
  | false, true , false, false, false => Some RV32IM
  | false, true , false, true, false  => Some RV32IMF
  | false, true , true , false, false => Some RV32IMA
  | false, true , true , true, false  => Some RV32IMAF
  | true , false, false, false, false => Some RV64I
  | true , false, false, true, false  => Some RV64IF
  | true , false, true , false, false => Some RV64IA
  | true , false, true , true, false  => Some RV64IAF
  | true , true , false, false, false => Some RV64IM
  | true , true , false, true, false  => Some RV64IMF
  | true , true , true , false, false => Some RV64IMA
  | true , true , true , true, false  => Some RV64IMAF
  | true, true, false, false, true => Some RV64IMV
  | _, _, _, _, _ => None
  end.

Definition fromInstructionSet(i: InstructionSet): InstructionSet' :=
  match i with
  | RV32I    => Build_InstructionSet' false false false false false
  | RV32IF   => Build_InstructionSet' false false false true  false
  | RV32IA   => Build_InstructionSet' false false true  false false
  | RV32IAF  => Build_InstructionSet' false false true  true  false
  | RV32IM   => Build_InstructionSet' false true  false false false
  | RV32IMF  => Build_InstructionSet' false true  false true  false
  | RV32IMA  => Build_InstructionSet' false true  true  false false
  | RV32IMAF => Build_InstructionSet' false true  true  true  false
  | RV64I    => Build_InstructionSet' true  false false false false
  | RV64IF   => Build_InstructionSet' true  false false true  false
  | RV64IA   => Build_InstructionSet' true  false true  false false
  | RV64IAF  => Build_InstructionSet' true  false true  true  false
  | RV64IM   => Build_InstructionSet' true  true  false false false
  | RV64IMF  => Build_InstructionSet' true  true  false true  false
  | RV64IMA  => Build_InstructionSet' true  true  true  false false
  | RV64IMAF => Build_InstructionSet' true  true  true  true  false
  | RV64IMV  => Build_InstructionSet' true  true  false false true
  end.

Lemma from_toInstructionSet: forall i, (i.(supports_V) = false) -> forall t, toInstructionSet i = Some t -> fromInstructionSet t = i.
Proof. intros. unfold toInstructionSet in *.
       all: destruct (supports_64bit i) eqn:E1; destruct (supports_M i) eqn:E2;
         destruct (supports_A i) eqn:E3; destruct (supports_F i) eqn:E4; destruct (supports_V i) eqn:E5.
       all: try solve [discriminate].
       all: inversion H0; simpl.
       all: destruct i.
       all: unfold supports_64bit, supports_M, supports_A, supports_F, supports_V in *.
       all: rewrite E1, E2, E3, E4, E5; reflexivity.
Qed.

Lemma to_fromInstructionSet: forall i, ((i = RV64IMV) -> False) -> toInstructionSet (fromInstructionSet i) = Some i.
Proof. destruct i; reflexivity. Qed.

Definition InstructionSet'_le(i1 i2: InstructionSet'): Prop :=
  Bool.le (supports_64bit i1) (supports_64bit i2) /\
  Bool.le (supports_M i1) (supports_M i2) /\
  Bool.le (supports_A i1) (supports_A i2) /\
  Bool.le (supports_F i1) (supports_F i2).

Lemma bitwidth_monotone: forall iset1 iset2,
    InstructionSet'_le (fromInstructionSet iset1) (fromInstructionSet iset2) ->
    bitwidth iset1 <= bitwidth iset2.
Proof. intros. destruct iset1; destruct iset2; cbv in *; intuition congruence. Qed.

Lemma bitwidth_cases: forall iset, bitwidth iset = 2 ^ 5 \/ bitwidth iset = 2 ^ 6.
Proof. destruct iset; cbn; auto. Qed.

Lemma verify_I_shift_66_monotone: forall iset1 iset2 opcode rd rs1 shamt6 funct3 funct6,
    InstructionSet'_le (fromInstructionSet iset1) (fromInstructionSet iset2) ->
    verify_I_shift_66 (bitwidth iset1) opcode rd rs1 shamt6 funct3 funct6 ->
    verify_I_shift_66 (bitwidth iset2) opcode rd rs1 shamt6 funct3 funct6.
Proof.
  unfold verify_I_shift_66. intros. apply bitwidth_monotone in H.
  pose proof bitwidth_cases iset2. intuition blia.
Qed.

Lemma respects_bounds_monotone: forall iset1 iset2 inst,
    InstructionSet'_le (fromInstructionSet iset1) (fromInstructionSet iset2) ->
    respects_bounds (bitwidth iset1) inst ->
    respects_bounds (bitwidth iset2) inst.
Proof.
  destruct inst; intros; try assumption.
  destruct iInstruction; try assumption.
  all: cbn in *.
  all: eauto using verify_I_shift_66_monotone.
Qed.

Lemma verify_iset_monotone: forall iset1 iset2 inst,
    InstructionSet'_le (fromInstructionSet iset1) (fromInstructionSet iset2) ->
    supportsF iset2 = false -> (* because verify_inst/decode_encode proofs don't support it yet *)
    supportsV iset2 = false ->
    verify_iset inst iset1 ->
    verify_iset inst iset2.
Proof.
  unfold verify_iset, InstructionSet'_le, Bool.le. destruct inst; auto.
  all: intros (L1 & L2 & L3 & L4) SF SV C.
  all: repeat match type of C with
             | _ \/ _ => destruct C as [? | C]
              end;
    subst; cbn in *.
  all: destruct iset2; cbn in *; try intuition congruence.
Qed.

Lemma verify_monotone: forall iset1 iset2 inst,
    InstructionSet'_le (fromInstructionSet iset1) (fromInstructionSet iset2) ->
    supportsF iset2 = false -> (* because verify_inst/decode_encode proofs don't support it yet *)
    supportsV iset2 = false ->
    verify inst iset1 ->
    verify inst iset2.
Proof.
  unfold verify. intuition eauto using verify_iset_monotone, respects_bounds_monotone.
Qed.

Lemma verify_iset_I_swap_extensions: forall iset1 iset2 inst,
    verify_iset (IInstruction inst) iset1 ->
    verify_iset (IInstruction inst) iset2.
Proof. unfold verify_iset. auto. Qed.

(* if verify_I holds for one set of extensions, it also holds for any other, because I is always included *)
Lemma verify_I_swap_extensions: forall iset1 iset2 inst,
    verify (IInstruction inst) iset1 ->
    bitwidth iset1 = bitwidth iset2 ->
    verify (IInstruction inst) iset2.
Proof.
  unfold verify.
  intros *. intros (R1 & R2) E. rewrite <- E. eauto using verify_iset_I_swap_extensions.
Qed.

(* if verify_CSR holds for one set of extensions, it also holds for any other, because CSR is always included *)
Lemma verify_CSR_swap_extensions: forall iset1 iset2 inst,
    verify (CSRInstruction inst) iset1 ->
    verify (CSRInstruction inst) iset2.
Proof.
  unfold verify. intros *. cbn. exact id.
Qed.
