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
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_at_eos_return_wit_1 : at_eos_return_wit_1.
Proof. Admitted. 

Lemma proof_of_at_eos_return_wit_2 : at_eos_return_wit_2.
Proof. Admitted. 

Lemma proof_of_peek_char_return_wit_1 : peek_char_return_wit_1.
Proof. Admitted. 

Lemma proof_of_peek_char_partial_solve_wit_1 : peek_char_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_get_char_safety_wit_1 : get_char_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_get_char_safety_wit_2 : get_char_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_get_char_return_wit_1 : get_char_return_wit_1.
Proof. Admitted. 

Lemma proof_of_get_char_partial_solve_wit_1 : get_char_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_ref_char_return_wit_1 : ref_char_return_wit_1.
Proof. Admitted. 

Lemma proof_of_is_digit_safety_wit_1 : is_digit_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_is_digit_safety_wit_2 : is_digit_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_is_digit_return_wit_1 : is_digit_return_wit_1.
Proof. Admitted. 

Lemma proof_of_is_digit_return_wit_2 : is_digit_return_wit_2.
Proof. Admitted. 

Lemma proof_of_is_digit_return_wit_3 : is_digit_return_wit_3.
Proof. Admitted. 

Lemma proof_of_token_is_null_safety_wit_1 : token_is_null_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_token_is_null_return_wit_1 : token_is_null_return_wit_1.
Proof. Admitted. 

Lemma proof_of_token_is_null_return_wit_2 : token_is_null_return_wit_2.
Proof. Admitted. 

Lemma proof_of_token_is_first_safety_wit_1 : token_is_first_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_token_is_first_safety_wit_2 : token_is_first_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_token_is_first_safety_wit_3 : token_is_first_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_token_is_first_return_wit_1 : token_is_first_return_wit_1.
Proof. Admitted. 

Lemma proof_of_token_is_first_return_wit_2 : token_is_first_return_wit_2.
Proof. Admitted. 

Lemma proof_of_token_is_last_safety_wit_1 : token_is_last_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_token_is_last_safety_wit_2 : token_is_last_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_token_is_last_return_wit_2 : token_is_last_return_wit_2.
Proof. Admitted. 

Lemma proof_of_mu_json_token_string_safety_wit_1 : mu_json_token_string_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mu_json_token_string_safety_wit_2 : mu_json_token_string_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_mu_json_token_string_safety_wit_3 : mu_json_token_string_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_mu_json_token_string_safety_wit_4 : mu_json_token_string_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_mu_json_token_string_safety_wit_5 : mu_json_token_string_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_mu_json_token_string_entail_wit_1_1 : mu_json_token_string_entail_wit_1_1.
Proof. Admitted. 

Lemma proof_of_mu_json_token_string_entail_wit_1_2 : mu_json_token_string_entail_wit_1_2.
Proof. Admitted. 

Lemma proof_of_mu_json_token_string_entail_wit_2_1 : mu_json_token_string_entail_wit_2_1.
Proof. Admitted. 

Lemma proof_of_mu_json_token_string_entail_wit_2_2 : mu_json_token_string_entail_wit_2_2.
Proof. Admitted. 

Lemma proof_of_mu_json_token_string_return_wit_1 : mu_json_token_string_return_wit_1.
Proof. Admitted. 

Lemma proof_of_mu_json_token_string_return_wit_2 : mu_json_token_string_return_wit_2.
Proof. Admitted. 

Lemma proof_of_mu_json_token_string_partial_solve_wit_1 : mu_json_token_string_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mu_json_token_string_partial_solve_wit_2 : mu_json_token_string_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mu_json_token_string_length_safety_wit_1 : mu_json_token_string_length_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mu_json_token_string_length_safety_wit_2 : mu_json_token_string_length_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_mu_json_token_string_length_safety_wit_3 : mu_json_token_string_length_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_mu_json_token_string_length_safety_wit_4 : mu_json_token_string_length_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_mu_json_token_string_length_safety_wit_5 : mu_json_token_string_length_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_mu_json_token_string_length_safety_wit_6 : mu_json_token_string_length_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_mu_json_token_string_length_safety_wit_7 : mu_json_token_string_length_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_mu_json_token_string_length_safety_wit_8 : mu_json_token_string_length_safety_wit_8.
Proof. Admitted. 

Lemma proof_of_mu_json_token_string_length_entail_wit_1_1 : mu_json_token_string_length_entail_wit_1_1.
Proof. Admitted. 

Lemma proof_of_mu_json_token_string_length_entail_wit_1_2 : mu_json_token_string_length_entail_wit_1_2.
Proof. Admitted. 

Lemma proof_of_mu_json_token_string_length_entail_wit_2_1 : mu_json_token_string_length_entail_wit_2_1.
Proof. Admitted. 

Lemma proof_of_mu_json_token_string_length_entail_wit_2_2 : mu_json_token_string_length_entail_wit_2_2.
Proof. Admitted. 

Lemma proof_of_mu_json_token_string_length_return_wit_1 : mu_json_token_string_length_return_wit_1.
Proof. Admitted. 

Lemma proof_of_mu_json_token_string_length_return_wit_2 : mu_json_token_string_length_return_wit_2.
Proof. Admitted. 

Lemma proof_of_mu_json_token_string_length_partial_solve_wit_1 : mu_json_token_string_length_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mu_json_token_string_length_partial_solve_wit_2 : mu_json_token_string_length_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mu_json_token_type_safety_wit_1 : mu_json_token_type_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mu_json_token_type_safety_wit_2 : mu_json_token_type_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_mu_json_token_type_safety_wit_3 : mu_json_token_type_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_mu_json_token_type_safety_wit_4 : mu_json_token_type_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_mu_json_token_type_safety_wit_5 : mu_json_token_type_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_mu_json_token_type_safety_wit_6 : mu_json_token_type_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_mu_json_token_type_safety_wit_7 : mu_json_token_type_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_mu_json_token_type_entail_wit_1_1 : mu_json_token_type_entail_wit_1_1.
Proof. Admitted. 

Lemma proof_of_mu_json_token_type_entail_wit_1_2 : mu_json_token_type_entail_wit_1_2.
Proof. Admitted. 

Lemma proof_of_mu_json_token_type_entail_wit_2_1 : mu_json_token_type_entail_wit_2_1.
Proof. Admitted. 

Lemma proof_of_mu_json_token_type_entail_wit_2_2 : mu_json_token_type_entail_wit_2_2.
Proof. Admitted. 

Lemma proof_of_mu_json_token_type_return_wit_1 : mu_json_token_type_return_wit_1.
Proof. Admitted. 

Lemma proof_of_mu_json_token_type_return_wit_2 : mu_json_token_type_return_wit_2.
Proof. Admitted. 

Lemma proof_of_mu_json_token_type_partial_solve_wit_1 : mu_json_token_type_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mu_json_token_type_partial_solve_wit_2 : mu_json_token_type_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mu_json_token_level_safety_wit_1 : mu_json_token_level_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mu_json_token_level_safety_wit_2 : mu_json_token_level_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_mu_json_token_level_safety_wit_3 : mu_json_token_level_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_mu_json_token_level_safety_wit_4 : mu_json_token_level_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_mu_json_token_level_safety_wit_5 : mu_json_token_level_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_mu_json_token_level_safety_wit_6 : mu_json_token_level_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_mu_json_token_level_safety_wit_7 : mu_json_token_level_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_mu_json_token_level_safety_wit_8 : mu_json_token_level_safety_wit_8.
Proof. Admitted. 

Lemma proof_of_mu_json_token_level_entail_wit_1_1 : mu_json_token_level_entail_wit_1_1.
Proof. Admitted. 

Lemma proof_of_mu_json_token_level_entail_wit_1_2 : mu_json_token_level_entail_wit_1_2.
Proof. Admitted. 

Lemma proof_of_mu_json_token_level_entail_wit_2_1 : mu_json_token_level_entail_wit_2_1.
Proof. Admitted. 

Lemma proof_of_mu_json_token_level_entail_wit_2_2 : mu_json_token_level_entail_wit_2_2.
Proof. Admitted. 

Lemma proof_of_mu_json_token_level_return_wit_1 : mu_json_token_level_return_wit_1.
Proof. Admitted. 

Lemma proof_of_mu_json_token_level_return_wit_2 : mu_json_token_level_return_wit_2.
Proof. Admitted. 

Lemma proof_of_mu_json_token_level_partial_solve_wit_1 : mu_json_token_level_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mu_json_token_level_partial_solve_wit_2 : mu_json_token_level_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mu_json_token_is_first_safety_wit_1 : mu_json_token_is_first_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mu_json_token_is_first_safety_wit_2 : mu_json_token_is_first_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_mu_json_token_is_first_safety_wit_3 : mu_json_token_is_first_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_mu_json_token_is_first_safety_wit_4 : mu_json_token_is_first_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_mu_json_token_is_first_safety_wit_5 : mu_json_token_is_first_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_mu_json_token_is_first_entail_wit_1_1 : mu_json_token_is_first_entail_wit_1_1.
Proof. Admitted. 

Lemma proof_of_mu_json_token_is_first_entail_wit_1_2 : mu_json_token_is_first_entail_wit_1_2.
Proof. Admitted. 

Lemma proof_of_mu_json_token_is_first_entail_wit_2_1 : mu_json_token_is_first_entail_wit_2_1.
Proof. Admitted. 

Lemma proof_of_mu_json_token_is_first_entail_wit_2_2 : mu_json_token_is_first_entail_wit_2_2.
Proof. Admitted. 

Lemma proof_of_mu_json_token_is_first_return_wit_1 : mu_json_token_is_first_return_wit_1.
Proof. Admitted. 

Lemma proof_of_mu_json_token_is_first_return_wit_2 : mu_json_token_is_first_return_wit_2.
Proof. Admitted. 

Lemma proof_of_mu_json_token_is_first_return_wit_3 : mu_json_token_is_first_return_wit_3.
Proof. Admitted. 

Lemma proof_of_mu_json_token_is_first_partial_solve_wit_1 : mu_json_token_is_first_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mu_json_token_is_first_partial_solve_wit_2 : mu_json_token_is_first_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mu_json_token_is_first_partial_solve_wit_3_pure : mu_json_token_is_first_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_mu_json_token_is_first_partial_solve_wit_3 : mu_json_token_is_first_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_mu_json_token_is_last_safety_wit_1 : mu_json_token_is_last_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mu_json_token_is_last_safety_wit_2 : mu_json_token_is_last_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_mu_json_token_is_last_safety_wit_3 : mu_json_token_is_last_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_mu_json_token_is_last_safety_wit_4 : mu_json_token_is_last_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_mu_json_token_is_last_safety_wit_5 : mu_json_token_is_last_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_mu_json_token_is_last_entail_wit_1_1 : mu_json_token_is_last_entail_wit_1_1.
Proof. Admitted. 

Lemma proof_of_mu_json_token_is_last_entail_wit_1_2 : mu_json_token_is_last_entail_wit_1_2.
Proof. Admitted. 

Lemma proof_of_mu_json_token_is_last_entail_wit_2_1 : mu_json_token_is_last_entail_wit_2_1.
Proof. Admitted. 

Lemma proof_of_mu_json_token_is_last_entail_wit_2_2 : mu_json_token_is_last_entail_wit_2_2.
Proof. Admitted. 

Lemma proof_of_mu_json_token_is_last_return_wit_1 : mu_json_token_is_last_return_wit_1.
Proof. Admitted. 

Lemma proof_of_mu_json_token_is_last_return_wit_2 : mu_json_token_is_last_return_wit_2.
Proof. Admitted. 

Lemma proof_of_mu_json_token_is_last_partial_solve_wit_1 : mu_json_token_is_last_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mu_json_token_is_last_partial_solve_wit_2 : mu_json_token_is_last_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mu_json_token_is_last_partial_solve_wit_3_pure : mu_json_token_is_last_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_mu_json_token_is_last_partial_solve_wit_3 : mu_json_token_is_last_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_skip_whitespace_safety_wit_1 : skip_whitespace_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_skip_whitespace_safety_wit_2 : skip_whitespace_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_skip_whitespace_safety_wit_3 : skip_whitespace_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_skip_whitespace_safety_wit_4 : skip_whitespace_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_skip_whitespace_safety_wit_5 : skip_whitespace_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_skip_whitespace_safety_wit_6 : skip_whitespace_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_skip_whitespace_entail_wit_2_1 : skip_whitespace_entail_wit_2_1.
Proof. Admitted. 

Lemma proof_of_skip_whitespace_entail_wit_2_2 : skip_whitespace_entail_wit_2_2.
Proof. Admitted. 

Lemma proof_of_skip_whitespace_entail_wit_2_3 : skip_whitespace_entail_wit_2_3.
Proof. Admitted. 

Lemma proof_of_skip_whitespace_entail_wit_2_4 : skip_whitespace_entail_wit_2_4.
Proof. Admitted. 

Lemma proof_of_skip_whitespace_partial_solve_wit_1_pure : skip_whitespace_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_skip_whitespace_partial_solve_wit_1 : skip_whitespace_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_skip_whitespace_partial_solve_wit_2_pure : skip_whitespace_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_skip_whitespace_partial_solve_wit_2 : skip_whitespace_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_skip_whitespace_partial_solve_wit_3_pure : skip_whitespace_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_skip_whitespace_partial_solve_wit_3 : skip_whitespace_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_skip_whitespace_partial_solve_wit_4_pure : skip_whitespace_partial_solve_wit_4_pure.
Proof. Admitted. 

Lemma proof_of_skip_whitespace_partial_solve_wit_4 : skip_whitespace_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_skip_whitespace_partial_solve_wit_5_pure : skip_whitespace_partial_solve_wit_5_pure.
Proof. Admitted. 

Lemma proof_of_skip_whitespace_partial_solve_wit_5 : skip_whitespace_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_skip_whitespace_partial_solve_wit_6_pure : skip_whitespace_partial_solve_wit_6_pure.
Proof. Admitted. 

Lemma proof_of_skip_whitespace_partial_solve_wit_6 : skip_whitespace_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_is_number_prefix_safety_wit_1 : is_number_prefix_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_is_number_prefix_safety_wit_2 : is_number_prefix_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_is_number_prefix_safety_wit_3 : is_number_prefix_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_is_number_prefix_return_wit_1 : is_number_prefix_return_wit_1.
Proof. Admitted. 

Lemma proof_of_is_number_prefix_return_wit_2 : is_number_prefix_return_wit_2.
Proof. Admitted. 

Lemma proof_of_is_number_prefix_return_wit_3 : is_number_prefix_return_wit_3.
Proof. Admitted. 

Lemma proof_of_is_number_prefix_return_wit_4 : is_number_prefix_return_wit_4.
Proof. Admitted. 

Lemma proof_of_is_hex_safety_wit_1 : is_hex_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_is_hex_safety_wit_2 : is_hex_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_is_hex_safety_wit_3 : is_hex_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_is_hex_safety_wit_4 : is_hex_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_is_hex_safety_wit_5 : is_hex_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_is_hex_safety_wit_6 : is_hex_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_is_hex_safety_wit_7 : is_hex_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_is_hex_safety_wit_8 : is_hex_safety_wit_8.
Proof. Admitted. 

Lemma proof_of_is_hex_safety_wit_9 : is_hex_safety_wit_9.
Proof. Admitted. 

Lemma proof_of_is_hex_safety_wit_10 : is_hex_safety_wit_10.
Proof. Admitted. 

Lemma proof_of_is_hex_safety_wit_11 : is_hex_safety_wit_11.
Proof. Admitted. 

Lemma proof_of_is_hex_safety_wit_12 : is_hex_safety_wit_12.
Proof. Admitted. 

Lemma proof_of_is_hex_return_wit_1 : is_hex_return_wit_1.
Proof. Admitted. 

Lemma proof_of_is_hex_return_wit_2 : is_hex_return_wit_2.
Proof. Admitted. 

Lemma proof_of_is_hex_return_wit_3 : is_hex_return_wit_3.
Proof. Admitted. 

Lemma proof_of_is_hex_return_wit_4 : is_hex_return_wit_4.
Proof. Admitted. 

Lemma proof_of_is_hex_return_wit_5 : is_hex_return_wit_5.
Proof. Admitted. 

Lemma proof_of_is_hex_return_wit_6 : is_hex_return_wit_6.
Proof. Admitted. 

Lemma proof_of_is_hex_return_wit_7 : is_hex_return_wit_7.
Proof. Admitted. 

Lemma proof_of_set_token_string_return_wit_1 : set_token_string_return_wit_1.
Proof. Admitted. 

Lemma proof_of_get_token_string_return_wit_1 : get_token_string_return_wit_1.
Proof. Admitted. 

Lemma proof_of_set_token_string_length_safety_wit_1 : set_token_string_length_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_set_token_string_length_safety_wit_2 : set_token_string_length_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_set_token_type_safety_wit_1 : set_token_type_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_set_token_type_safety_wit_2 : set_token_type_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_set_token_level_safety_wit_1 : set_token_level_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_set_token_level_safety_wit_2 : set_token_level_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_set_token_is_last_safety_wit_1 : set_token_is_last_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_set_token_is_last_safety_wit_2 : set_token_is_last_safety_wit_2.
Proof. Admitted. 

