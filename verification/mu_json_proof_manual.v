Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.QCP_demos_LLM.mu_json Require Import mu_json_goal.
From SimpleC.EE.QCP_demos_LLM.mu_json Require Import mu_json_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_token_is_last_return_wit_1_split_goal_1 : token_is_last_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  assert (Hmask : 0 <= Z.land (Z.shiftr w 31) 1 < 2).
  { change (0 <= Z.land (Z.shiftr w 31) (Z.ones 1) < 2).
    rewrite Z.land_ones by lia.
    change (0 <= (Z.shiftr w 31) mod 2 < 2).
    apply Z.mod_pos_bound; lia. }
  lia.
Qed.

Lemma proof_of_token_is_last_return_wit_1 : token_is_last_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_token_is_last_return_wit_1_split_goal_1.
Qed. 

Lemma proof_of_skip_whitespace_entail_wit_1_split_goal_1 : skip_whitespace_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_skip_whitespace_entail_wit_1 : skip_whitespace_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_skip_whitespace_entail_wit_1_split_goal_1.
Qed. 

Lemma proof_of_skip_whitespace_return_wit_1 : skip_whitespace_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia).
  assert (p_str_pos = n) by lia. subst p_str_pos.
  Left.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; lia.
Qed. 

Lemma proof_of_skip_whitespace_return_wit_2 : skip_whitespace_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia).
  Right. Exists p_str_pos.
  split_pure_spatial.
  - cancel.
    cancel ((&((p_pre) # "parser" ->ₛ "str")) # Ptr |-> s).
    cancel.
  - split_pures; dump_pre_spatial; subst; intuition lia.
Qed. 

Lemma proof_of_set_token_string_length_return_wit_1_split_goal_1 : set_token_string_length_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  f_equal.
  apply unsigned_last_nbits_eq.
  rewrite Z.shiftl_mul_pow2 by lia.
  change (0 <= Z.land string_length_pre (Z.ones 16) * 1 < 4294967296).
  rewrite Z.land_ones by lia.
  change (0 <= (string_length_pre mod 65536) * 1 < 4294967296).
  pose proof (Z.mod_pos_bound string_length_pre 65536 ltac:(lia)) as Hmask.
  lia.
Qed.

Lemma proof_of_set_token_string_length_return_wit_1_split_goal_2 : set_token_string_length_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  f_equal.
  apply unsigned_last_nbits_eq.
  rewrite Z.shiftl_mul_pow2 by lia.
  change (0 <= Z.land string_length_pre (Z.ones 16) * 1 < 4294967296).
  rewrite Z.land_ones by lia.
  change (0 <= (string_length_pre mod 65536) * 1 < 4294967296).
  pose proof (Z.mod_pos_bound string_length_pre 65536 ltac:(lia)) as Hmask.
  lia.
Qed.

Lemma proof_of_set_token_string_length_return_wit_1 : set_token_string_length_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_set_token_string_length_return_wit_1_split_goal_1.
  - Goal_apply proof_of_set_token_string_length_return_wit_1_split_goal_2.
Qed. 

Lemma proof_of_set_token_type_return_wit_1_split_goal_1 : set_token_type_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  f_equal.
  apply unsigned_last_nbits_eq.
  rewrite Z.shiftl_mul_pow2 by lia.
  change (0 <= Z.land token_type_pre (Z.ones 4) * 65536 < 4294967296).
  rewrite Z.land_ones by lia.
  change (0 <= (token_type_pre mod 16) * 65536 < 4294967296).
  pose proof (Z.mod_pos_bound token_type_pre 16 ltac:(lia)) as Hmask.
  lia.
Qed.

Lemma proof_of_set_token_type_return_wit_1_split_goal_2 : set_token_type_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  f_equal.
  apply unsigned_last_nbits_eq.
  rewrite Z.shiftl_mul_pow2 by lia.
  change (0 <= Z.land token_type_pre (Z.ones 4) * 65536 < 4294967296).
  rewrite Z.land_ones by lia.
  change (0 <= (token_type_pre mod 16) * 65536 < 4294967296).
  pose proof (Z.mod_pos_bound token_type_pre 16 ltac:(lia)) as Hmask.
  lia.
Qed.

Lemma proof_of_set_token_type_return_wit_1 : set_token_type_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_set_token_type_return_wit_1_split_goal_1.
  - Goal_apply proof_of_set_token_type_return_wit_1_split_goal_2.
Qed. 

Lemma proof_of_set_token_level_return_wit_1_split_goal_1 : set_token_level_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  f_equal.
  apply unsigned_last_nbits_eq.
  rewrite Z.shiftl_mul_pow2 by lia.
  change (0 <= Z.land level_pre (Z.ones 11) * 1048576 < 4294967296).
  rewrite Z.land_ones by lia.
  change (0 <= (level_pre mod 2048) * 1048576 < 4294967296).
  pose proof (Z.mod_pos_bound level_pre 2048 ltac:(lia)) as Hmask.
  lia.
Qed.

Lemma proof_of_set_token_level_return_wit_1_split_goal_2 : set_token_level_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  f_equal.
  apply unsigned_last_nbits_eq.
  rewrite Z.shiftl_mul_pow2 by lia.
  change (0 <= Z.land level_pre (Z.ones 11) * 1048576 < 4294967296).
  rewrite Z.land_ones by lia.
  change (0 <= (level_pre mod 2048) * 1048576 < 4294967296).
  pose proof (Z.mod_pos_bound level_pre 2048 ltac:(lia)) as Hmask.
  lia.
Qed.

Lemma proof_of_set_token_level_return_wit_1 : set_token_level_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_set_token_level_return_wit_1_split_goal_1.
  - Goal_apply proof_of_set_token_level_return_wit_1_split_goal_2.
Qed. 

Lemma proof_of_set_token_is_last_return_wit_1_split_goal_1 : set_token_is_last_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  f_equal.
  apply unsigned_last_nbits_eq.
  rewrite Z.shiftl_mul_pow2 by lia.
  change (0 <= Z.land is_last_pre (Z.ones 1) * 2147483648 < 4294967296).
  rewrite Z.land_ones by lia.
  change (0 <= (is_last_pre mod 2) * 2147483648 < 4294967296).
  pose proof (Z.mod_pos_bound is_last_pre 2 ltac:(lia)) as Hmask.
  lia.
Qed.

Lemma proof_of_set_token_is_last_return_wit_1_split_goal_2 : set_token_is_last_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  f_equal.
  apply unsigned_last_nbits_eq.
  rewrite Z.shiftl_mul_pow2 by lia.
  change (0 <= Z.land is_last_pre (Z.ones 1) * 2147483648 < 4294967296).
  rewrite Z.land_ones by lia.
  change (0 <= (is_last_pre mod 2) * 2147483648 < 4294967296).
  pose proof (Z.mod_pos_bound is_last_pre 2 ltac:(lia)) as Hmask.
  lia.
Qed.

Lemma proof_of_set_token_is_last_return_wit_1 : set_token_is_last_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_set_token_is_last_return_wit_1_split_goal_1.
  - Goal_apply proof_of_set_token_is_last_return_wit_1_split_goal_2.
Qed. 

