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
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

(*----- Function at_eos -----*)

Definition at_eos_return_wit_1 := 
forall (p_pre: Z) (len: Z) (pos: Z) (PreH1 : (pos >= len)) (PreH2 : (INT_MIN <= pos)) (PreH3 : (pos <= INT_MAX)) (PreH4 : (INT_MIN <= len)) (PreH5 : (len <= INT_MAX)) ,
  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> pos)
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> len)
|--
  “ (1 = 1) ” 
  &&  “ (pos >= len) ”
  &&  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> pos)
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> len)
.

Definition at_eos_return_wit_2 := 
forall (p_pre: Z) (len: Z) (pos: Z) (PreH1 : (pos < len)) (PreH2 : (INT_MIN <= pos)) (PreH3 : (pos <= INT_MAX)) (PreH4 : (INT_MIN <= len)) (PreH5 : (len <= INT_MAX)) ,
  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> pos)
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> len)
|--
  “ (0 = 0) ” 
  &&  “ (pos < len) ”
  &&  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> pos)
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> len)
.

(*----- Function peek_char -----*)

Definition peek_char_return_wit_1 := 
forall (p_pre: Z) (l: (@list Z)) (n: Z) (pos: Z) (s: Z) (PreH1 : (0 <= pos)) (PreH2 : (pos < n)) (PreH3 : (n <= INT_MAX)) ,
  (CharArray.full s n l )
  **  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> pos)
|--
  “ ((Znth pos l 0) = (Znth (pos) (l) (0))) ”
  &&  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> pos)
  **  (CharArray.full s n l )
.

Definition peek_char_partial_solve_wit_1 := 
forall (p_pre: Z) (l: (@list Z)) (n: Z) (pos: Z) (s: Z) (PreH1 : (0 <= pos)) (PreH2 : (pos < n)) (PreH3 : (n <= INT_MAX)) ,
  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> pos)
  **  (CharArray.full s n l )
|--
  “ (0 <= pos) ” 
  &&  “ (pos < n) ” 
  &&  “ (n <= INT_MAX) ”
  &&  (((s + (pos * sizeof(CHAR)))) # Char  |-> (Znth pos l 0))
  **  (CharArray.missing_i s pos 0 n l )
  **  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> pos)
.

(*----- Function get_char -----*)

Definition get_char_safety_wit_1 := 
forall (p_pre: Z) (l: (@list Z)) (n: Z) (pos: Z) (s: Z) (PreH1 : (0 <= pos)) (PreH2 : (pos < n)) (PreH3 : (n <= INT_MAX)) ,
  (CharArray.full s n l )
  **  ((( &( "ch" ) )) # Char  |-> (Znth pos l 0))
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> pos)
|--
  “ ((pos + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pos + 1 )) ”
.

Definition get_char_safety_wit_2 := 
forall (p_pre: Z) (l: (@list Z)) (n: Z) (pos: Z) (s: Z) (PreH1 : (0 <= pos)) (PreH2 : (pos < n)) (PreH3 : (n <= INT_MAX)) ,
  (CharArray.full s n l )
  **  ((( &( "ch" ) )) # Char  |-> (Znth pos l 0))
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> pos)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_char_return_wit_1 := 
forall (p_pre: Z) (l: (@list Z)) (n: Z) (pos: Z) (s: Z) (PreH1 : (0 <= pos)) (PreH2 : (pos < n)) (PreH3 : (n <= INT_MAX)) ,
  (CharArray.full s n l )
  **  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> (pos + 1 ))
|--
  EX (p_pre_str_pos: Z) ,
  “ ((Znth pos l 0) = (Znth (pos) (l) (0))) ” 
  &&  “ (p_pre_str_pos = (pos + 1 )) ”
  &&  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_pre_str_pos)
  **  (CharArray.full s n l )
.

Definition get_char_partial_solve_wit_1 := 
forall (p_pre: Z) (l: (@list Z)) (n: Z) (pos: Z) (s: Z) (PreH1 : (0 <= pos)) (PreH2 : (pos < n)) (PreH3 : (n <= INT_MAX)) ,
  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> pos)
  **  (CharArray.full s n l )
|--
  “ (0 <= pos) ” 
  &&  “ (pos < n) ” 
  &&  “ (n <= INT_MAX) ”
  &&  (((s + (pos * sizeof(CHAR)))) # Char  |-> (Znth pos l 0))
  **  (CharArray.missing_i s pos 0 n l )
  **  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> pos)
.

(*----- Function ref_char -----*)

Definition ref_char_return_wit_1 := 
forall (p_pre: Z) (l: (@list Z)) (n: Z) (pos: Z) (s: Z) (PreH1 : (0 <= pos)) (PreH2 : (pos <= n)) (PreH3 : (n <= INT_MAX)) ,
  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> pos)
  **  (CharArray.full s n l )
|--
  “ ((s + (pos * sizeof(CHAR))) = (s + pos )) ”
  &&  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> pos)
  **  (CharArray.full s n l )
.

(*----- Function is_digit -----*)

Definition is_digit_safety_wit_1 := 
forall (ch_pre: Z) (PreH1 : ((-128) <= ch_pre)) (PreH2 : (ch_pre <= 255)) ,
  ((( &( "ch" ) )) # Char  |-> ch_pre)
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition is_digit_safety_wit_2 := 
forall (ch_pre: Z) (PreH1 : (ch_pre >= 48)) (PreH2 : ((-128) <= ch_pre)) (PreH3 : (ch_pre <= 255)) ,
  ((( &( "ch" ) )) # Char  |-> ch_pre)
|--
  “ (57 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 57) ”
.

Definition is_digit_return_wit_1 := 
forall (ch_pre: Z) (PreH1 : (ch_pre > 57)) (PreH2 : (ch_pre >= 48)) (PreH3 : ((-128) <= ch_pre)) (PreH4 : (ch_pre <= 255)) ,
  TT && emp 
|--
  “ (0 = 0) ” 
  &&  “ (57 < ch_pre) ”
  &&  emp
.

Definition is_digit_return_wit_2 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <= 57)) (PreH2 : (ch_pre >= 48)) (PreH3 : ((-128) <= ch_pre)) (PreH4 : (ch_pre <= 255)) ,
  TT && emp 
|--
  “ (1 = 1) ” 
  &&  “ (48 <= ch_pre) ” 
  &&  “ (ch_pre <= 57) ”
  &&  emp
.

Definition is_digit_return_wit_3 := 
forall (ch_pre: Z) (PreH1 : (ch_pre < 48)) (PreH2 : ((-128) <= ch_pre)) (PreH3 : (ch_pre <= 255)) ,
  TT && emp 
|--
  “ (0 = 0) ” 
  &&  “ (ch_pre < 48) ”
  &&  emp
.

(*----- Function token_is_null -----*)

Definition token_is_null_safety_wit_1 := 
forall (token_pre: Z) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition token_is_null_return_wit_1 := 
forall (token_pre: Z) (PreH1 : (token_pre = 0)) ,
  TT && emp 
|--
  “ (1 = 1) ” 
  &&  “ (token_pre = 0) ”
  &&  emp
.

Definition token_is_null_return_wit_2 := 
forall (token_pre: Z) (PreH1 : (token_pre <> 0)) ,
  TT && emp 
|--
  “ (0 = 0) ” 
  &&  “ (token_pre <> 0) ”
  &&  emp
.

(*----- Function token_is_first -----*)

Definition token_is_first_safety_wit_1 := 
forall (token_pre: Z) (w: Z) (PreH1 : (0 <= w)) (PreH2 : (w <= UINT_MAX)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
  **  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (20 <= 31) ” 
  &&  “ (0 <= 20) ”
.

Definition token_is_first_safety_wit_2 := 
forall (token_pre: Z) (w: Z) (PreH1 : (0 <= w)) (PreH2 : (w <= UINT_MAX)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
  **  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (20 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 20) ”
.

Definition token_is_first_safety_wit_3 := 
forall (token_pre: Z) (w: Z) (PreH1 : (0 <= w)) (PreH2 : (w <= UINT_MAX)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
  **  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition token_is_first_return_wit_1 := 
forall (token_pre: Z) (w: Z) (PreH1 : ((Z.land (Z.shiftr w 20) 2047) = 0)) (PreH2 : (0 <= w)) (PreH3 : (w <= UINT_MAX)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (1 = 1) ” 
  &&  “ ((Z.land (Z.shiftr w 20) 2047) = 0) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
.

Definition token_is_first_return_wit_2 := 
forall (token_pre: Z) (w: Z) (PreH1 : ((Z.land (Z.shiftr w 20) 2047) <> 0)) (PreH2 : (0 <= w)) (PreH3 : (w <= UINT_MAX)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (0 = 0) ” 
  &&  “ ((Z.land (Z.shiftr w 20) 2047) <> 0) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
.

(*----- Function token_is_last -----*)

Definition token_is_last_safety_wit_1 := 
forall (token_pre: Z) (w: Z) (PreH1 : (0 <= w)) (PreH2 : (w <= UINT_MAX)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
  **  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (31 <= 31) ” 
  &&  “ (0 <= 31) ”
.

Definition token_is_last_safety_wit_2 := 
forall (token_pre: Z) (w: Z) (PreH1 : (0 <= w)) (PreH2 : (w <= UINT_MAX)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
  **  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (31 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 31) ”
.

Definition token_is_last_return_wit_1 := 
(
forall (token_pre: Z) (w: Z) (PreH1 : ((Z.land (Z.shiftr w 31) 1) <> 0)) (PreH2 : (0 <= w)) (PreH3 : (w <= UINT_MAX)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (1 = (Z.land (Z.shiftr w 31) 1)) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
) \/
(
forall (w: Z) (PreH1 : ((Z.land (Z.shiftr w 31) 1) <> 0)) (PreH2 : (0 <= w)) (PreH3 : (w <= UINT_MAX)) ,
  TT && emp 
|--
  “ (1 = (Z.land (Z.shiftr w 31) 1)) ”
  &&  emp
).

Definition token_is_last_return_wit_1_split_goal_1 := 
forall (w: Z) (PreH1 : ((Z.land (Z.shiftr w 31) 1) <> 0)) (PreH2 : (0 <= w)) (PreH3 : (w <= UINT_MAX)) ,
  (1 = (Z.land (Z.shiftr w 31) 1))
.

Definition token_is_last_return_wit_2 := 
forall (token_pre: Z) (w: Z) (PreH1 : ((Z.land (Z.shiftr w 31) 1) = 0)) (PreH2 : (0 <= w)) (PreH3 : (w <= UINT_MAX)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (0 = (Z.land (Z.shiftr w 31) 1)) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
.

(*----- Function mu_json_parse_str -----*)

(*----- Function mu_json_parse_buffer -----*)

(*----- Function mu_json_error_name -----*)

(*----- Function mu_json_token_string -----*)

Definition mu_json_token_string_safety_wit_1 := 
forall (token_pre: Z) (s: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre = 0)) (PreH4 : (s = 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
|--
  “ False ”
.

Definition mu_json_token_string_safety_wit_2 := 
forall (token_pre: Z) (s: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre <> 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
  **  ((&((token_pre)  # "anonymous struct 1" ->ₛ "str")) # Ptr  |-> s)
|--
  “ False ”
.

Definition mu_json_token_string_safety_wit_3 := 
forall (token_pre: Z) (s: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre = 0)) (PreH4 : (s = 0)) (PreH5 : (retval = 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
|--
  “ False ”
.

Definition mu_json_token_string_safety_wit_4 := 
forall (token_pre: Z) (s: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (retval <> 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
  **  ((&((token_pre)  # "anonymous struct 1" ->ₛ "str")) # Ptr  |-> s)
|--
  “ False ”
.

Definition mu_json_token_string_safety_wit_5 := 
forall (token_pre: Z) (s: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre = 0)) (PreH4 : (s = 0)) (PreH5 : (retval <> 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mu_json_token_string_entail_wit_1_1 := 
forall (token_pre: Z) (s: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre = 0)) (PreH4 : (s = 0)) (PreH5 : (retval_2 = 0)) ,
  TT && emp 
|--
  EX (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (token_pre <> 0) ” 
  &&  “ (token_pre <> 0) ” 
  &&  “ (retval = 0) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "str")) # Ptr  |-> s)
.

Definition mu_json_token_string_entail_wit_1_2 := 
forall (token_pre: Z) (s: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (retval = 0)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "str")) # Ptr  |-> s)
|--
  “ (retval = 0) ” 
  &&  “ (token_pre <> 0) ” 
  &&  “ (token_pre <> 0) ” 
  &&  “ (retval = 0) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "str")) # Ptr  |-> s)
.

Definition mu_json_token_string_entail_wit_2_1 := 
forall (token_pre: Z) (s: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre = 0)) (PreH4 : (s = 0)) (PreH5 : (retval <> 0)) ,
  TT && emp 
|--
  “ (retval = 1) ” 
  &&  “ (token_pre = 0) ” 
  &&  “ (token_pre = 0) ” 
  &&  “ (s = 0) ” 
  &&  “ (retval <> 0) ”
  &&  emp
.

Definition mu_json_token_string_entail_wit_2_2 := 
forall (token_pre: Z) (s: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (retval_2 <> 0)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "str")) # Ptr  |-> s)
|--
  EX (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ (token_pre = 0) ” 
  &&  “ (token_pre = 0) ” 
  &&  “ (s = 0) ” 
  &&  “ (retval <> 0) ”
  &&  emp
.

Definition mu_json_token_string_return_wit_1 := 
forall (token_pre: Z) (s: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (retval = 0)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "str")) # Ptr  |-> s)
|--
  “ (s = s) ” 
  &&  “ (token_pre <> 0) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "str")) # Ptr  |-> s)
.

Definition mu_json_token_string_return_wit_2 := 
forall (token_pre: Z) (s: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre = 0)) (PreH4 : (s = 0)) (PreH5 : (retval <> 0)) ,
  TT && emp 
|--
  “ (0 = s) ” 
  &&  “ (token_pre = 0) ” 
  &&  “ (s = 0) ”
  &&  emp
.

Definition mu_json_token_string_partial_solve_wit_1 := 
forall (token_pre: Z) (s: Z) (PreH1 : (token_pre = 0)) (PreH2 : (s = 0)) ,
  TT && emp 
|--
  “ (token_pre = 0) ” 
  &&  “ (s = 0) ”
  &&  emp
.

Definition mu_json_token_string_partial_solve_wit_2 := 
forall (token_pre: Z) (s: Z) (PreH1 : (token_pre <> 0)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "str")) # Ptr  |-> s)
|--
  “ (token_pre <> 0) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "str")) # Ptr  |-> s)
.

(*----- Function mu_json_token_string_length -----*)

Definition mu_json_token_string_length_safety_wit_1 := 
forall (token_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre = 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
|--
  “ False ”
.

Definition mu_json_token_string_length_safety_wit_2 := 
forall (token_pre: Z) (w: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (0 <= w)) (PreH5 : (w <= UINT_MAX)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
  **  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ False ”
.

Definition mu_json_token_string_length_safety_wit_3 := 
forall (token_pre: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre = 0)) (PreH4 : (retval = 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
|--
  “ False ”
.

Definition mu_json_token_string_length_safety_wit_4 := 
forall (token_pre: Z) (w: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (0 <= w)) (PreH5 : (w <= UINT_MAX)) (PreH6 : (retval <> 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
  **  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ False ”
.

Definition mu_json_token_string_length_safety_wit_5 := 
forall (token_pre: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre = 0)) (PreH4 : (retval <> 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition mu_json_token_string_length_safety_wit_6 := 
forall (token_pre: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre = 0)) (PreH4 : (retval <> 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mu_json_token_string_length_safety_wit_7 := 
forall (token_pre: Z) (w: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (0 <= w)) (PreH5 : (w <= UINT_MAX)) (PreH6 : (retval = 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
  **  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (0 <= 31) ” 
  &&  “ (0 <= 0) ”
.

Definition mu_json_token_string_length_safety_wit_8 := 
forall (token_pre: Z) (w: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (0 <= w)) (PreH5 : (w <= UINT_MAX)) (PreH6 : (retval = 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
  **  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mu_json_token_string_length_entail_wit_1_1 := 
forall (token_pre: Z) (w: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre = 0)) (PreH4 : (retval_2 = 0)) ,
  TT && emp 
|--
  EX (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (token_pre <> 0) ” 
  &&  “ (token_pre <> 0) ” 
  &&  “ (0 <= w) ” 
  &&  “ (w <= UINT_MAX) ” 
  &&  “ (retval = 0) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
.

Definition mu_json_token_string_length_entail_wit_1_2 := 
forall (token_pre: Z) (w: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (0 <= w)) (PreH5 : (w <= UINT_MAX)) (PreH6 : (retval = 0)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (retval = 0) ” 
  &&  “ (token_pre <> 0) ” 
  &&  “ (token_pre <> 0) ” 
  &&  “ (0 <= w) ” 
  &&  “ (w <= UINT_MAX) ” 
  &&  “ (retval = 0) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
.

Definition mu_json_token_string_length_entail_wit_2_1 := 
forall (token_pre: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre = 0)) (PreH4 : (retval <> 0)) ,
  TT && emp 
|--
  “ (retval = 1) ” 
  &&  “ (token_pre = 0) ” 
  &&  “ (token_pre = 0) ” 
  &&  “ (retval <> 0) ”
  &&  emp
.

Definition mu_json_token_string_length_entail_wit_2_2 := 
forall (token_pre: Z) (w: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (0 <= w)) (PreH5 : (w <= UINT_MAX)) (PreH6 : (retval_2 <> 0)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  EX (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ (token_pre = 0) ” 
  &&  “ (token_pre = 0) ” 
  &&  “ (retval <> 0) ”
  &&  emp
.

Definition mu_json_token_string_length_return_wit_1 := 
forall (token_pre: Z) (w: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (0 <= w)) (PreH5 : (w <= UINT_MAX)) (PreH6 : (retval = 0)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (token_pre <> 0) ” 
  &&  “ ((Z.land (Z.shiftr w 0) 65535) = (Z.land (Z.shiftr w 0) 65535)) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
.

Definition mu_json_token_string_length_return_wit_2 := 
forall (token_pre: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre = 0)) (PreH4 : (retval <> 0)) ,
  TT && emp 
|--
  “ (token_pre = 0) ” 
  &&  “ ((-1) = (-1)) ”
  &&  emp
.

Definition mu_json_token_string_length_partial_solve_wit_1 := 
forall (token_pre: Z) (PreH1 : (token_pre = 0)) ,
  TT && emp 
|--
  “ (token_pre = 0) ”
  &&  emp
.

Definition mu_json_token_string_length_partial_solve_wit_2 := 
forall (token_pre: Z) (w: Z) (PreH1 : (token_pre <> 0)) (PreH2 : (0 <= w)) (PreH3 : (w <= UINT_MAX)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (token_pre <> 0) ” 
  &&  “ (0 <= w) ” 
  &&  “ (w <= UINT_MAX) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
.

(*----- Function mu_json_token_type -----*)

Definition mu_json_token_type_safety_wit_1 := 
forall (token_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre = 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
|--
  “ False ”
.

Definition mu_json_token_type_safety_wit_2 := 
forall (token_pre: Z) (w: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (0 <= w)) (PreH5 : (w <= UINT_MAX)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
  **  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ False ”
.

Definition mu_json_token_type_safety_wit_3 := 
forall (token_pre: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre = 0)) (PreH4 : (retval = 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
|--
  “ False ”
.

Definition mu_json_token_type_safety_wit_4 := 
forall (token_pre: Z) (w: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (0 <= w)) (PreH5 : (w <= UINT_MAX)) (PreH6 : (retval <> 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
  **  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ False ”
.

Definition mu_json_token_type_safety_wit_5 := 
forall (token_pre: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre = 0)) (PreH4 : (retval <> 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mu_json_token_type_safety_wit_6 := 
forall (token_pre: Z) (w: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (0 <= w)) (PreH5 : (w <= UINT_MAX)) (PreH6 : (retval = 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
  **  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (16 <= 31) ” 
  &&  “ (0 <= 16) ”
.

Definition mu_json_token_type_safety_wit_7 := 
forall (token_pre: Z) (w: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (0 <= w)) (PreH5 : (w <= UINT_MAX)) (PreH6 : (retval = 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
  **  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (16 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 16) ”
.

Definition mu_json_token_type_entail_wit_1_1 := 
forall (token_pre: Z) (w: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre = 0)) (PreH4 : (retval_2 = 0)) ,
  TT && emp 
|--
  EX (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (token_pre <> 0) ” 
  &&  “ (token_pre <> 0) ” 
  &&  “ (0 <= w) ” 
  &&  “ (w <= UINT_MAX) ” 
  &&  “ (retval = 0) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
.

Definition mu_json_token_type_entail_wit_1_2 := 
forall (token_pre: Z) (w: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (0 <= w)) (PreH5 : (w <= UINT_MAX)) (PreH6 : (retval = 0)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (retval = 0) ” 
  &&  “ (token_pre <> 0) ” 
  &&  “ (token_pre <> 0) ” 
  &&  “ (0 <= w) ” 
  &&  “ (w <= UINT_MAX) ” 
  &&  “ (retval = 0) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
.

Definition mu_json_token_type_entail_wit_2_1 := 
forall (token_pre: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre = 0)) (PreH4 : (retval <> 0)) ,
  TT && emp 
|--
  “ (retval = 1) ” 
  &&  “ (token_pre = 0) ” 
  &&  “ (token_pre = 0) ” 
  &&  “ (retval <> 0) ”
  &&  emp
.

Definition mu_json_token_type_entail_wit_2_2 := 
forall (token_pre: Z) (w: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (0 <= w)) (PreH5 : (w <= UINT_MAX)) (PreH6 : (retval_2 <> 0)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  EX (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ (token_pre = 0) ” 
  &&  “ (token_pre = 0) ” 
  &&  “ (retval <> 0) ”
  &&  emp
.

Definition mu_json_token_type_return_wit_1 := 
forall (token_pre: Z) (w: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (0 <= w)) (PreH5 : (w <= UINT_MAX)) (PreH6 : (retval = 0)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (token_pre <> 0) ” 
  &&  “ ((Z.land (Z.shiftr w 16) 15) = (Z.land (Z.shiftr w 16) 15)) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
.

Definition mu_json_token_type_return_wit_2 := 
forall (token_pre: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre = 0)) (PreH4 : (retval <> 0)) ,
  TT && emp 
|--
  “ (token_pre = 0) ” 
  &&  “ (0 = 0) ”
  &&  emp
.

Definition mu_json_token_type_partial_solve_wit_1 := 
forall (token_pre: Z) (PreH1 : (token_pre = 0)) ,
  TT && emp 
|--
  “ (token_pre = 0) ”
  &&  emp
.

Definition mu_json_token_type_partial_solve_wit_2 := 
forall (token_pre: Z) (w: Z) (PreH1 : (token_pre <> 0)) (PreH2 : (0 <= w)) (PreH3 : (w <= UINT_MAX)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (token_pre <> 0) ” 
  &&  “ (0 <= w) ” 
  &&  “ (w <= UINT_MAX) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
.

(*----- Function mu_json_token_level -----*)

Definition mu_json_token_level_safety_wit_1 := 
forall (token_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre = 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
|--
  “ False ”
.

Definition mu_json_token_level_safety_wit_2 := 
forall (token_pre: Z) (w: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (0 <= w)) (PreH5 : (w <= UINT_MAX)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
  **  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ False ”
.

Definition mu_json_token_level_safety_wit_3 := 
forall (token_pre: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre = 0)) (PreH4 : (retval = 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
|--
  “ False ”
.

Definition mu_json_token_level_safety_wit_4 := 
forall (token_pre: Z) (w: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (0 <= w)) (PreH5 : (w <= UINT_MAX)) (PreH6 : (retval <> 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
  **  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ False ”
.

Definition mu_json_token_level_safety_wit_5 := 
forall (token_pre: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre = 0)) (PreH4 : (retval <> 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition mu_json_token_level_safety_wit_6 := 
forall (token_pre: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre = 0)) (PreH4 : (retval <> 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mu_json_token_level_safety_wit_7 := 
forall (token_pre: Z) (w: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (0 <= w)) (PreH5 : (w <= UINT_MAX)) (PreH6 : (retval = 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
  **  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (20 <= 31) ” 
  &&  “ (0 <= 20) ”
.

Definition mu_json_token_level_safety_wit_8 := 
forall (token_pre: Z) (w: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (0 <= w)) (PreH5 : (w <= UINT_MAX)) (PreH6 : (retval = 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
  **  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (20 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 20) ”
.

Definition mu_json_token_level_entail_wit_1_1 := 
forall (token_pre: Z) (w: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre = 0)) (PreH4 : (retval_2 = 0)) ,
  TT && emp 
|--
  EX (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (token_pre <> 0) ” 
  &&  “ (token_pre <> 0) ” 
  &&  “ (0 <= w) ” 
  &&  “ (w <= UINT_MAX) ” 
  &&  “ (retval = 0) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
.

Definition mu_json_token_level_entail_wit_1_2 := 
forall (token_pre: Z) (w: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (0 <= w)) (PreH5 : (w <= UINT_MAX)) (PreH6 : (retval = 0)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (retval = 0) ” 
  &&  “ (token_pre <> 0) ” 
  &&  “ (token_pre <> 0) ” 
  &&  “ (0 <= w) ” 
  &&  “ (w <= UINT_MAX) ” 
  &&  “ (retval = 0) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
.

Definition mu_json_token_level_entail_wit_2_1 := 
forall (token_pre: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre = 0)) (PreH4 : (retval <> 0)) ,
  TT && emp 
|--
  “ (retval = 1) ” 
  &&  “ (token_pre = 0) ” 
  &&  “ (token_pre = 0) ” 
  &&  “ (retval <> 0) ”
  &&  emp
.

Definition mu_json_token_level_entail_wit_2_2 := 
forall (token_pre: Z) (w: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (0 <= w)) (PreH5 : (w <= UINT_MAX)) (PreH6 : (retval_2 <> 0)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  EX (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ (token_pre = 0) ” 
  &&  “ (token_pre = 0) ” 
  &&  “ (retval <> 0) ”
  &&  emp
.

Definition mu_json_token_level_return_wit_1 := 
forall (token_pre: Z) (w: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (0 <= w)) (PreH5 : (w <= UINT_MAX)) (PreH6 : (retval = 0)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (token_pre <> 0) ” 
  &&  “ ((Z.land (Z.shiftr w 20) 2047) = (Z.land (Z.shiftr w 20) 2047)) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
.

Definition mu_json_token_level_return_wit_2 := 
forall (token_pre: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre = 0)) (PreH4 : (retval <> 0)) ,
  TT && emp 
|--
  “ (token_pre = 0) ” 
  &&  “ ((-1) = (-1)) ”
  &&  emp
.

Definition mu_json_token_level_partial_solve_wit_1 := 
forall (token_pre: Z) (PreH1 : (token_pre = 0)) ,
  TT && emp 
|--
  “ (token_pre = 0) ”
  &&  emp
.

Definition mu_json_token_level_partial_solve_wit_2 := 
forall (token_pre: Z) (w: Z) (PreH1 : (token_pre <> 0)) (PreH2 : (0 <= w)) (PreH3 : (w <= UINT_MAX)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (token_pre <> 0) ” 
  &&  “ (0 <= w) ” 
  &&  “ (w <= UINT_MAX) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
.

(*----- Function mu_json_token_is_first -----*)

Definition mu_json_token_is_first_safety_wit_1 := 
forall (token_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre = 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
|--
  “ False ”
.

Definition mu_json_token_is_first_safety_wit_2 := 
forall (token_pre: Z) (w: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (0 <= w)) (PreH5 : (w <= UINT_MAX)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
  **  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ False ”
.

Definition mu_json_token_is_first_safety_wit_3 := 
forall (token_pre: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre = 0)) (PreH4 : (retval = 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
|--
  “ False ”
.

Definition mu_json_token_is_first_safety_wit_4 := 
forall (token_pre: Z) (w: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (0 <= w)) (PreH5 : (w <= UINT_MAX)) (PreH6 : (retval <> 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
  **  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ False ”
.

Definition mu_json_token_is_first_safety_wit_5 := 
forall (token_pre: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre = 0)) (PreH4 : (retval <> 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mu_json_token_is_first_entail_wit_1_1 := 
forall (token_pre: Z) (w: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre = 0)) (PreH4 : (retval_2 = 0)) ,
  TT && emp 
|--
  EX (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (token_pre <> 0) ” 
  &&  “ (token_pre <> 0) ” 
  &&  “ (0 <= w) ” 
  &&  “ (w <= UINT_MAX) ” 
  &&  “ (retval = 0) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
.

Definition mu_json_token_is_first_entail_wit_1_2 := 
forall (token_pre: Z) (w: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (0 <= w)) (PreH5 : (w <= UINT_MAX)) (PreH6 : (retval = 0)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (retval = 0) ” 
  &&  “ (token_pre <> 0) ” 
  &&  “ (token_pre <> 0) ” 
  &&  “ (0 <= w) ” 
  &&  “ (w <= UINT_MAX) ” 
  &&  “ (retval = 0) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
.

Definition mu_json_token_is_first_entail_wit_2_1 := 
forall (token_pre: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre = 0)) (PreH4 : (retval <> 0)) ,
  TT && emp 
|--
  “ (retval = 1) ” 
  &&  “ (token_pre = 0) ” 
  &&  “ (token_pre = 0) ” 
  &&  “ (retval <> 0) ”
  &&  emp
.

Definition mu_json_token_is_first_entail_wit_2_2 := 
forall (token_pre: Z) (w: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (0 <= w)) (PreH5 : (w <= UINT_MAX)) (PreH6 : (retval_2 <> 0)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  EX (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ (token_pre = 0) ” 
  &&  “ (token_pre = 0) ” 
  &&  “ (retval <> 0) ”
  &&  emp
.

Definition mu_json_token_is_first_return_wit_1 := 
forall (token_pre: Z) (w: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((Z.land (Z.shiftr w 20) 2047) <> 0)) (PreH3 : (retval_2 = 0)) (PreH4 : (token_pre <> 0)) (PreH5 : (token_pre <> 0)) (PreH6 : (0 <= w)) (PreH7 : (w <= UINT_MAX)) (PreH8 : (retval_2 = 0)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (token_pre <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ ((Z.land (Z.shiftr w 20) 2047) <> 0) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
.

Definition mu_json_token_is_first_return_wit_2 := 
forall (token_pre: Z) (w: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : ((Z.land (Z.shiftr w 20) 2047) = 0)) (PreH3 : (retval_2 = 0)) (PreH4 : (token_pre <> 0)) (PreH5 : (token_pre <> 0)) (PreH6 : (0 <= w)) (PreH7 : (w <= UINT_MAX)) (PreH8 : (retval_2 = 0)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (token_pre <> 0) ” 
  &&  “ (retval = 1) ” 
  &&  “ ((Z.land (Z.shiftr w 20) 2047) = 0) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
.

Definition mu_json_token_is_first_return_wit_3 := 
forall (token_pre: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre = 0)) (PreH4 : (retval <> 0)) ,
  TT && emp 
|--
  “ (token_pre = 0) ” 
  &&  “ (0 = 0) ”
  &&  emp
.

Definition mu_json_token_is_first_partial_solve_wit_1 := 
forall (token_pre: Z) (PreH1 : (token_pre = 0)) ,
  TT && emp 
|--
  “ (token_pre = 0) ”
  &&  emp
.

Definition mu_json_token_is_first_partial_solve_wit_2 := 
forall (token_pre: Z) (w: Z) (PreH1 : (token_pre <> 0)) (PreH2 : (0 <= w)) (PreH3 : (w <= UINT_MAX)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (token_pre <> 0) ” 
  &&  “ (0 <= w) ” 
  &&  “ (w <= UINT_MAX) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
.

Definition mu_json_token_is_first_partial_solve_wit_3_pure := 
forall (token_pre: Z) (w: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (0 <= w)) (PreH5 : (w <= UINT_MAX)) (PreH6 : (retval = 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
  **  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (0 <= w) ” 
  &&  “ (w <= UINT_MAX) ”
.

Definition mu_json_token_is_first_partial_solve_wit_3_aux := 
forall (token_pre: Z) (w: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (0 <= w)) (PreH5 : (w <= UINT_MAX)) (PreH6 : (retval = 0)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (0 <= w) ” 
  &&  “ (w <= UINT_MAX) ” 
  &&  “ (retval = 0) ” 
  &&  “ (token_pre <> 0) ” 
  &&  “ (token_pre <> 0) ” 
  &&  “ (0 <= w) ” 
  &&  “ (w <= UINT_MAX) ” 
  &&  “ (retval = 0) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
.

Definition mu_json_token_is_first_partial_solve_wit_3 := mu_json_token_is_first_partial_solve_wit_3_pure -> mu_json_token_is_first_partial_solve_wit_3_aux.

(*----- Function mu_json_token_is_last -----*)

Definition mu_json_token_is_last_safety_wit_1 := 
forall (token_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre = 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
|--
  “ False ”
.

Definition mu_json_token_is_last_safety_wit_2 := 
forall (token_pre: Z) (w: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (0 <= w)) (PreH5 : (w <= UINT_MAX)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
  **  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ False ”
.

Definition mu_json_token_is_last_safety_wit_3 := 
forall (token_pre: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre = 0)) (PreH4 : (retval = 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
|--
  “ False ”
.

Definition mu_json_token_is_last_safety_wit_4 := 
forall (token_pre: Z) (w: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (0 <= w)) (PreH5 : (w <= UINT_MAX)) (PreH6 : (retval <> 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
  **  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ False ”
.

Definition mu_json_token_is_last_safety_wit_5 := 
forall (token_pre: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre = 0)) (PreH4 : (retval <> 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mu_json_token_is_last_entail_wit_1_1 := 
forall (token_pre: Z) (w: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre = 0)) (PreH4 : (retval_2 = 0)) ,
  TT && emp 
|--
  EX (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (token_pre <> 0) ” 
  &&  “ (token_pre <> 0) ” 
  &&  “ (0 <= w) ” 
  &&  “ (w <= UINT_MAX) ” 
  &&  “ (retval = 0) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
.

Definition mu_json_token_is_last_entail_wit_1_2 := 
forall (token_pre: Z) (w: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (0 <= w)) (PreH5 : (w <= UINT_MAX)) (PreH6 : (retval = 0)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (retval = 0) ” 
  &&  “ (token_pre <> 0) ” 
  &&  “ (token_pre <> 0) ” 
  &&  “ (0 <= w) ” 
  &&  “ (w <= UINT_MAX) ” 
  &&  “ (retval = 0) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
.

Definition mu_json_token_is_last_entail_wit_2_1 := 
forall (token_pre: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre = 0)) (PreH4 : (retval <> 0)) ,
  TT && emp 
|--
  “ (retval = 1) ” 
  &&  “ (token_pre = 0) ” 
  &&  “ (token_pre = 0) ” 
  &&  “ (retval <> 0) ”
  &&  emp
.

Definition mu_json_token_is_last_entail_wit_2_2 := 
forall (token_pre: Z) (w: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (0 <= w)) (PreH5 : (w <= UINT_MAX)) (PreH6 : (retval_2 <> 0)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  EX (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ (token_pre = 0) ” 
  &&  “ (token_pre = 0) ” 
  &&  “ (retval <> 0) ”
  &&  emp
.

Definition mu_json_token_is_last_return_wit_1 := 
forall (token_pre: Z) (w: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (Z.land (Z.shiftr w 31) 1))) (PreH2 : (retval_2 = 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (token_pre <> 0)) (PreH5 : (0 <= w)) (PreH6 : (w <= UINT_MAX)) (PreH7 : (retval_2 = 0)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (token_pre <> 0) ” 
  &&  “ (retval = (Z.land (Z.shiftr w 31) 1)) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
.

Definition mu_json_token_is_last_return_wit_2 := 
forall (token_pre: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (token_pre = 0)) (PreH3 : (token_pre = 0)) (PreH4 : (retval <> 0)) ,
  TT && emp 
|--
  “ (token_pre = 0) ” 
  &&  “ (0 = 0) ”
  &&  emp
.

Definition mu_json_token_is_last_partial_solve_wit_1 := 
forall (token_pre: Z) (PreH1 : (token_pre = 0)) ,
  TT && emp 
|--
  “ (token_pre = 0) ”
  &&  emp
.

Definition mu_json_token_is_last_partial_solve_wit_2 := 
forall (token_pre: Z) (w: Z) (PreH1 : (token_pre <> 0)) (PreH2 : (0 <= w)) (PreH3 : (w <= UINT_MAX)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (token_pre <> 0) ” 
  &&  “ (0 <= w) ” 
  &&  “ (w <= UINT_MAX) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
.

Definition mu_json_token_is_last_partial_solve_wit_3_pure := 
forall (token_pre: Z) (w: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (0 <= w)) (PreH5 : (w <= UINT_MAX)) (PreH6 : (retval = 0)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
  **  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (0 <= w) ” 
  &&  “ (w <= UINT_MAX) ”
.

Definition mu_json_token_is_last_partial_solve_wit_3_aux := 
forall (token_pre: Z) (w: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (token_pre <> 0)) (PreH3 : (token_pre <> 0)) (PreH4 : (0 <= w)) (PreH5 : (w <= UINT_MAX)) (PreH6 : (retval = 0)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (0 <= w) ” 
  &&  “ (w <= UINT_MAX) ” 
  &&  “ (retval = 0) ” 
  &&  “ (token_pre <> 0) ” 
  &&  “ (token_pre <> 0) ” 
  &&  “ (0 <= w) ” 
  &&  “ (w <= UINT_MAX) ” 
  &&  “ (retval = 0) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
.

Definition mu_json_token_is_last_partial_solve_wit_3 := mu_json_token_is_last_partial_solve_wit_3_pure -> mu_json_token_is_last_partial_solve_wit_3_aux.

(*----- Function mu_json_find_root_token -----*)

(*----- Function mu_json_find_next_token -----*)

(*----- Function mu_json_find_prev_token -----*)

(*----- Function mu_json_find_parent_token -----*)

(*----- Function mu_json_find_child_token -----*)

(*----- Function mu_json_find_next_sibling_token -----*)

(*----- Function mu_json_find_prev_sibling_token -----*)

(*----- Function skip_whitespace -----*)

Definition skip_whitespace_safety_wit_1 := 
forall (p_pre: Z) (l: (@list Z)) (n: Z) (start: Z) (s: Z) (p_str_pos: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 0)) (PreH3 : (p_str_pos < n)) (PreH4 : (0 <= start)) (PreH5 : (start <= p_str_pos)) (PreH6 : (p_str_pos <= n)) (PreH7 : (n <= INT_MAX)) (PreH8 : forall (i: Z) , (((start <= i) /\ (i < p_str_pos)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13)))) ,
  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_str_pos)
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  (CharArray.full s n l )
|--
  “ False ”
.

Definition skip_whitespace_safety_wit_2 := 
forall (p_pre: Z) (l: (@list Z)) (n: Z) (start: Z) (s: Z) (p_str_pos: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 1)) (PreH3 : (p_str_pos >= n)) (PreH4 : (0 <= start)) (PreH5 : (start <= p_str_pos)) (PreH6 : (p_str_pos <= n)) (PreH7 : (n <= INT_MAX)) (PreH8 : forall (i: Z) , (((start <= i) /\ (i < p_str_pos)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13)))) ,
  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_str_pos)
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  (CharArray.full s n l )
|--
  “ False ”
.

Definition skip_whitespace_safety_wit_3 := 
forall (p_pre: Z) (l: (@list Z)) (n: Z) (start: Z) (s: Z) (p_str_pos: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Znth (p_str_pos) (l) (0)))) (PreH2 : (retval = 0)) (PreH3 : (retval = 0)) (PreH4 : (p_str_pos < n)) (PreH5 : (0 <= start)) (PreH6 : (start <= p_str_pos)) (PreH7 : (p_str_pos <= n)) (PreH8 : (n <= INT_MAX)) (PreH9 : forall (i: Z) , (((start <= i) /\ (i < p_str_pos)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13)))) ,
  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_str_pos)
  **  (CharArray.full s n l )
  **  ((( &( "ch" ) )) # Char  |-> retval_2)
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition skip_whitespace_safety_wit_4 := 
forall (p_pre: Z) (l: (@list Z)) (n: Z) (start: Z) (s: Z) (p_str_pos: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 32)) (PreH2 : (retval_2 = (Znth (p_str_pos) (l) (0)))) (PreH3 : (retval = 0)) (PreH4 : (retval = 0)) (PreH5 : (p_str_pos < n)) (PreH6 : (0 <= start)) (PreH7 : (start <= p_str_pos)) (PreH8 : (p_str_pos <= n)) (PreH9 : (n <= INT_MAX)) (PreH10 : forall (i: Z) , (((start <= i) /\ (i < p_str_pos)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13)))) ,
  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_str_pos)
  **  (CharArray.full s n l )
  **  ((( &( "ch" ) )) # Char  |-> retval_2)
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (9 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 9) ”
.

Definition skip_whitespace_safety_wit_5 := 
forall (p_pre: Z) (l: (@list Z)) (n: Z) (start: Z) (s: Z) (p_str_pos: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 9)) (PreH2 : (retval_2 <> 32)) (PreH3 : (retval_2 = (Znth (p_str_pos) (l) (0)))) (PreH4 : (retval = 0)) (PreH5 : (retval = 0)) (PreH6 : (p_str_pos < n)) (PreH7 : (0 <= start)) (PreH8 : (start <= p_str_pos)) (PreH9 : (p_str_pos <= n)) (PreH10 : (n <= INT_MAX)) (PreH11 : forall (i: Z) , (((start <= i) /\ (i < p_str_pos)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13)))) ,
  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_str_pos)
  **  (CharArray.full s n l )
  **  ((( &( "ch" ) )) # Char  |-> retval_2)
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition skip_whitespace_safety_wit_6 := 
forall (p_pre: Z) (l: (@list Z)) (n: Z) (start: Z) (s: Z) (p_str_pos: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 10)) (PreH2 : (retval_2 <> 9)) (PreH3 : (retval_2 <> 32)) (PreH4 : (retval_2 = (Znth (p_str_pos) (l) (0)))) (PreH5 : (retval = 0)) (PreH6 : (retval = 0)) (PreH7 : (p_str_pos < n)) (PreH8 : (0 <= start)) (PreH9 : (start <= p_str_pos)) (PreH10 : (p_str_pos <= n)) (PreH11 : (n <= INT_MAX)) (PreH12 : forall (i: Z) , (((start <= i) /\ (i < p_str_pos)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13)))) ,
  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_str_pos)
  **  (CharArray.full s n l )
  **  ((( &( "ch" ) )) # Char  |-> retval_2)
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (13 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 13) ”
.

Definition skip_whitespace_entail_wit_1 := 
(
forall (p_pre: Z) (l: (@list Z)) (n: Z) (start: Z) (s: Z) (PreH1 : (0 <= start)) (PreH2 : (start <= n)) (PreH3 : (n <= INT_MAX)) ,
  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> start)
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
  **  (CharArray.full s n l )
|--
  EX (p_str_pos: Z) ,
  “ (0 <= start) ” 
  &&  “ (start <= p_str_pos) ” 
  &&  “ (p_str_pos <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ forall (i: Z) , (((start <= i) /\ (i < p_str_pos)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13))) ”
  &&  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_str_pos)
  **  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
  **  (CharArray.full s n l )
) \/
(
forall (l: (@list Z)) (n: Z) (start: Z) (PreH1 : (0 <= start)) (PreH2 : (start <= n)) (PreH3 : (n <= INT_MAX)) ,
  TT && emp 
|--
  “ forall (i: Z) , (((start <= i) /\ (i < start)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13))) ”
  &&  emp
).

Definition skip_whitespace_entail_wit_1_split_goal_1 := 
forall (l: (@list Z)) (n: Z) (start: Z) (PreH1 : (0 <= start)) (PreH2 : (start <= n)) (PreH3 : (n <= INT_MAX)) ,
  forall (i: Z) , (((start <= i) /\ (i < start)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13)))
.

Definition skip_whitespace_entail_wit_2_1 := 
forall (p_pre: Z) (l: (@list Z)) (n: Z) (start: Z) (s: Z) (p_str_pos_2: Z) (retval: Z) (retval_2: Z) (p_callee_str_pos: Z) (retval_3: Z) (PreH1 : (retval_3 = (Znth (p_str_pos_2) (l) (0)))) (PreH2 : (p_callee_str_pos = (p_str_pos_2 + 1 ))) (PreH3 : (retval_2 = 10)) (PreH4 : (retval_2 <> 9)) (PreH5 : (retval_2 <> 32)) (PreH6 : (retval_2 = (Znth (p_str_pos_2) (l) (0)))) (PreH7 : (retval = 0)) (PreH8 : (retval = 0)) (PreH9 : (p_str_pos_2 < n)) (PreH10 : (0 <= start)) (PreH11 : (start <= p_str_pos_2)) (PreH12 : (p_str_pos_2 <= n)) (PreH13 : (n <= INT_MAX)) (PreH14 : forall (i: Z) , (((start <= i) /\ (i < p_str_pos_2)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13)))) ,
  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_callee_str_pos)
  **  (CharArray.full s n l )
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
|--
  EX (p_str_pos: Z) ,
  “ (0 <= start) ” 
  &&  “ (start <= p_str_pos) ” 
  &&  “ (p_str_pos <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ forall (i: Z) , (((start <= i) /\ (i < p_str_pos)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13))) ”
  &&  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_str_pos)
  **  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
  **  (CharArray.full s n l )
.

Definition skip_whitespace_entail_wit_2_2 := 
forall (p_pre: Z) (l: (@list Z)) (n: Z) (start: Z) (s: Z) (p_str_pos_2: Z) (retval: Z) (retval_2: Z) (p_callee_str_pos: Z) (retval_3: Z) (PreH1 : (retval_3 = (Znth (p_str_pos_2) (l) (0)))) (PreH2 : (p_callee_str_pos = (p_str_pos_2 + 1 ))) (PreH3 : (retval_2 = 32)) (PreH4 : (retval_2 = (Znth (p_str_pos_2) (l) (0)))) (PreH5 : (retval = 0)) (PreH6 : (retval = 0)) (PreH7 : (p_str_pos_2 < n)) (PreH8 : (0 <= start)) (PreH9 : (start <= p_str_pos_2)) (PreH10 : (p_str_pos_2 <= n)) (PreH11 : (n <= INT_MAX)) (PreH12 : forall (i: Z) , (((start <= i) /\ (i < p_str_pos_2)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13)))) ,
  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_callee_str_pos)
  **  (CharArray.full s n l )
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
|--
  EX (p_str_pos: Z) ,
  “ (0 <= start) ” 
  &&  “ (start <= p_str_pos) ” 
  &&  “ (p_str_pos <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ forall (i: Z) , (((start <= i) /\ (i < p_str_pos)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13))) ”
  &&  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_str_pos)
  **  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
  **  (CharArray.full s n l )
.

Definition skip_whitespace_entail_wit_2_3 := 
forall (p_pre: Z) (l: (@list Z)) (n: Z) (start: Z) (s: Z) (p_str_pos_2: Z) (retval: Z) (retval_2: Z) (p_callee_str_pos: Z) (retval_3: Z) (PreH1 : (retval_3 = (Znth (p_str_pos_2) (l) (0)))) (PreH2 : (p_callee_str_pos = (p_str_pos_2 + 1 ))) (PreH3 : (retval_2 = 9)) (PreH4 : (retval_2 <> 32)) (PreH5 : (retval_2 = (Znth (p_str_pos_2) (l) (0)))) (PreH6 : (retval = 0)) (PreH7 : (retval = 0)) (PreH8 : (p_str_pos_2 < n)) (PreH9 : (0 <= start)) (PreH10 : (start <= p_str_pos_2)) (PreH11 : (p_str_pos_2 <= n)) (PreH12 : (n <= INT_MAX)) (PreH13 : forall (i: Z) , (((start <= i) /\ (i < p_str_pos_2)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13)))) ,
  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_callee_str_pos)
  **  (CharArray.full s n l )
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
|--
  EX (p_str_pos: Z) ,
  “ (0 <= start) ” 
  &&  “ (start <= p_str_pos) ” 
  &&  “ (p_str_pos <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ forall (i: Z) , (((start <= i) /\ (i < p_str_pos)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13))) ”
  &&  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_str_pos)
  **  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
  **  (CharArray.full s n l )
.

Definition skip_whitespace_entail_wit_2_4 := 
forall (p_pre: Z) (l: (@list Z)) (n: Z) (start: Z) (s: Z) (p_str_pos_2: Z) (retval: Z) (retval_2: Z) (p_callee_str_pos: Z) (retval_3: Z) (PreH1 : (retval_3 = (Znth (p_str_pos_2) (l) (0)))) (PreH2 : (p_callee_str_pos = (p_str_pos_2 + 1 ))) (PreH3 : (retval_2 = 13)) (PreH4 : (retval_2 <> 10)) (PreH5 : (retval_2 <> 9)) (PreH6 : (retval_2 <> 32)) (PreH7 : (retval_2 = (Znth (p_str_pos_2) (l) (0)))) (PreH8 : (retval = 0)) (PreH9 : (retval = 0)) (PreH10 : (p_str_pos_2 < n)) (PreH11 : (0 <= start)) (PreH12 : (start <= p_str_pos_2)) (PreH13 : (p_str_pos_2 <= n)) (PreH14 : (n <= INT_MAX)) (PreH15 : forall (i: Z) , (((start <= i) /\ (i < p_str_pos_2)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13)))) ,
  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_callee_str_pos)
  **  (CharArray.full s n l )
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
|--
  EX (p_str_pos: Z) ,
  “ (0 <= start) ” 
  &&  “ (start <= p_str_pos) ” 
  &&  “ (p_str_pos <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ forall (i: Z) , (((start <= i) /\ (i < p_str_pos)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13))) ”
  &&  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_str_pos)
  **  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
  **  (CharArray.full s n l )
.

Definition skip_whitespace_return_wit_1 := 
forall (p_pre: Z) (l: (@list Z)) (n: Z) (start: Z) (s: Z) (p_str_pos: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 1)) (PreH3 : (p_str_pos >= n)) (PreH4 : (0 <= start)) (PreH5 : (start <= p_str_pos)) (PreH6 : (p_str_pos <= n)) (PreH7 : (n <= INT_MAX)) (PreH8 : forall (i_2: Z) , (((start <= i_2) /\ (i_2 < p_str_pos)) -> (((((Znth (i_2) (l) (0)) = 32) \/ ((Znth (i_2) (l) (0)) = 9)) \/ ((Znth (i_2) (l) (0)) = 10)) \/ ((Znth (i_2) (l) (0)) = 13)))) ,
  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_str_pos)
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
  **  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  (CharArray.full s n l )
|--
  (“ (start <= n) ” 
  &&  “ (n <= n) ” 
  &&  “ forall (i: Z) , (((start <= i) /\ (i < n)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13))) ”
  &&  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> n)
  **  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
  **  (CharArray.full s n l ))
  ||
  (EX (p_pre_str_pos: Z) ,
  “ (start <= p_pre_str_pos) ” 
  &&  “ (p_pre_str_pos <= n) ” 
  &&  “ forall (i: Z) , (((start <= i) /\ (i < p_pre_str_pos)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13))) ” 
  &&  “ (p_pre_str_pos < n) ” 
  &&  “ ~((((((Znth (p_pre_str_pos) (l) (0)) = 32) \/ ((Znth (p_pre_str_pos) (l) (0)) = 9)) \/ ((Znth (p_pre_str_pos) (l) (0)) = 10)) \/ ((Znth (p_pre_str_pos) (l) (0)) = 13))) ”
  &&  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_pre_str_pos)
  **  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
  **  (CharArray.full s n l ))
.

Definition skip_whitespace_return_wit_2 := 
forall (p_pre: Z) (l: (@list Z)) (n: Z) (start: Z) (s: Z) (p_str_pos: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 13)) (PreH2 : (retval_2 <> 10)) (PreH3 : (retval_2 <> 9)) (PreH4 : (retval_2 <> 32)) (PreH5 : (retval_2 = (Znth (p_str_pos) (l) (0)))) (PreH6 : (retval = 0)) (PreH7 : (retval = 0)) (PreH8 : (p_str_pos < n)) (PreH9 : (0 <= start)) (PreH10 : (start <= p_str_pos)) (PreH11 : (p_str_pos <= n)) (PreH12 : (n <= INT_MAX)) (PreH13 : forall (i_2: Z) , (((start <= i_2) /\ (i_2 < p_str_pos)) -> (((((Znth (i_2) (l) (0)) = 32) \/ ((Znth (i_2) (l) (0)) = 9)) \/ ((Znth (i_2) (l) (0)) = 10)) \/ ((Znth (i_2) (l) (0)) = 13)))) ,
  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_str_pos)
  **  (CharArray.full s n l )
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
|--
  (“ (start <= n) ” 
  &&  “ (n <= n) ” 
  &&  “ forall (i: Z) , (((start <= i) /\ (i < n)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13))) ”
  &&  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> n)
  **  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
  **  (CharArray.full s n l ))
  ||
  (EX (p_pre_str_pos: Z) ,
  “ (start <= p_pre_str_pos) ” 
  &&  “ (p_pre_str_pos <= n) ” 
  &&  “ forall (i: Z) , (((start <= i) /\ (i < p_pre_str_pos)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13))) ” 
  &&  “ (p_pre_str_pos < n) ” 
  &&  “ ~((((((Znth (p_pre_str_pos) (l) (0)) = 32) \/ ((Znth (p_pre_str_pos) (l) (0)) = 9)) \/ ((Znth (p_pre_str_pos) (l) (0)) = 10)) \/ ((Znth (p_pre_str_pos) (l) (0)) = 13))) ”
  &&  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_pre_str_pos)
  **  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
  **  (CharArray.full s n l ))
.

Definition skip_whitespace_partial_solve_wit_1_pure := 
forall (p_pre: Z) (l: (@list Z)) (n: Z) (start: Z) (s: Z) (p_str_pos: Z) (PreH1 : (0 <= start)) (PreH2 : (start <= p_str_pos)) (PreH3 : (p_str_pos <= n)) (PreH4 : (n <= INT_MAX)) (PreH5 : forall (i: Z) , (((start <= i) /\ (i < p_str_pos)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13)))) ,
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_str_pos)
  **  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
  **  (CharArray.full s n l )
|--
  “ (INT_MIN <= p_str_pos) ” 
  &&  “ (p_str_pos <= INT_MAX) ” 
  &&  “ (INT_MIN <= n) ” 
  &&  “ (n <= INT_MAX) ”
.

Definition skip_whitespace_partial_solve_wit_1_aux := 
forall (p_pre: Z) (l: (@list Z)) (n: Z) (start: Z) (s: Z) (p_str_pos: Z) (PreH1 : (0 <= start)) (PreH2 : (start <= p_str_pos)) (PreH3 : (p_str_pos <= n)) (PreH4 : (n <= INT_MAX)) (PreH5 : forall (i: Z) , (((start <= i) /\ (i < p_str_pos)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13)))) ,
  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_str_pos)
  **  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
  **  (CharArray.full s n l )
|--
  “ (INT_MIN <= p_str_pos) ” 
  &&  “ (p_str_pos <= INT_MAX) ” 
  &&  “ (INT_MIN <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start <= p_str_pos) ” 
  &&  “ (p_str_pos <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ forall (i: Z) , (((start <= i) /\ (i < p_str_pos)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13))) ”
  &&  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_str_pos)
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
  **  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  (CharArray.full s n l )
.

Definition skip_whitespace_partial_solve_wit_1 := skip_whitespace_partial_solve_wit_1_pure -> skip_whitespace_partial_solve_wit_1_aux.

Definition skip_whitespace_partial_solve_wit_2_pure := 
forall (p_pre: Z) (l: (@list Z)) (n: Z) (start: Z) (s: Z) (p_str_pos: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (p_str_pos < n)) (PreH4 : (0 <= start)) (PreH5 : (start <= p_str_pos)) (PreH6 : (p_str_pos <= n)) (PreH7 : (n <= INT_MAX)) (PreH8 : forall (i: Z) , (((start <= i) /\ (i < p_str_pos)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13)))) ,
  ((( &( "ch" ) )) # Char  |->_)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_str_pos)
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  (CharArray.full s n l )
|--
  “ (0 <= p_str_pos) ” 
  &&  “ (p_str_pos < n) ” 
  &&  “ (n <= INT_MAX) ”
.

Definition skip_whitespace_partial_solve_wit_2_aux := 
forall (p_pre: Z) (l: (@list Z)) (n: Z) (start: Z) (s: Z) (p_str_pos: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (p_str_pos < n)) (PreH4 : (0 <= start)) (PreH5 : (start <= p_str_pos)) (PreH6 : (p_str_pos <= n)) (PreH7 : (n <= INT_MAX)) (PreH8 : forall (i: Z) , (((start <= i) /\ (i < p_str_pos)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13)))) ,
  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_str_pos)
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
  **  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  (CharArray.full s n l )
|--
  “ (0 <= p_str_pos) ” 
  &&  “ (p_str_pos < n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (p_str_pos < n) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start <= p_str_pos) ” 
  &&  “ (p_str_pos <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ forall (i: Z) , (((start <= i) /\ (i < p_str_pos)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13))) ”
  &&  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_str_pos)
  **  (CharArray.full s n l )
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
.

Definition skip_whitespace_partial_solve_wit_2 := skip_whitespace_partial_solve_wit_2_pure -> skip_whitespace_partial_solve_wit_2_aux.

Definition skip_whitespace_partial_solve_wit_3_pure := 
forall (p_pre: Z) (l: (@list Z)) (n: Z) (start: Z) (s: Z) (p_str_pos: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 10)) (PreH2 : (retval_2 <> 9)) (PreH3 : (retval_2 <> 32)) (PreH4 : (retval_2 = (Znth (p_str_pos) (l) (0)))) (PreH5 : (retval = 0)) (PreH6 : (retval = 0)) (PreH7 : (p_str_pos < n)) (PreH8 : (0 <= start)) (PreH9 : (start <= p_str_pos)) (PreH10 : (p_str_pos <= n)) (PreH11 : (n <= INT_MAX)) (PreH12 : forall (i: Z) , (((start <= i) /\ (i < p_str_pos)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13)))) ,
  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_str_pos)
  **  (CharArray.full s n l )
  **  ((( &( "ch" ) )) # Char  |-> retval_2)
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (0 <= p_str_pos) ” 
  &&  “ (p_str_pos < n) ” 
  &&  “ (n <= INT_MAX) ”
.

Definition skip_whitespace_partial_solve_wit_3_aux := 
forall (p_pre: Z) (l: (@list Z)) (n: Z) (start: Z) (s: Z) (p_str_pos: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 10)) (PreH2 : (retval_2 <> 9)) (PreH3 : (retval_2 <> 32)) (PreH4 : (retval_2 = (Znth (p_str_pos) (l) (0)))) (PreH5 : (retval = 0)) (PreH6 : (retval = 0)) (PreH7 : (p_str_pos < n)) (PreH8 : (0 <= start)) (PreH9 : (start <= p_str_pos)) (PreH10 : (p_str_pos <= n)) (PreH11 : (n <= INT_MAX)) (PreH12 : forall (i: Z) , (((start <= i) /\ (i < p_str_pos)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13)))) ,
  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_str_pos)
  **  (CharArray.full s n l )
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
|--
  “ (0 <= p_str_pos) ” 
  &&  “ (p_str_pos < n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (retval_2 = 10) ” 
  &&  “ (retval_2 <> 9) ” 
  &&  “ (retval_2 <> 32) ” 
  &&  “ (retval_2 = (Znth (p_str_pos) (l) (0))) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (p_str_pos < n) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start <= p_str_pos) ” 
  &&  “ (p_str_pos <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ forall (i: Z) , (((start <= i) /\ (i < p_str_pos)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13))) ”
  &&  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_str_pos)
  **  (CharArray.full s n l )
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
.

Definition skip_whitespace_partial_solve_wit_3 := skip_whitespace_partial_solve_wit_3_pure -> skip_whitespace_partial_solve_wit_3_aux.

Definition skip_whitespace_partial_solve_wit_4_pure := 
forall (p_pre: Z) (l: (@list Z)) (n: Z) (start: Z) (s: Z) (p_str_pos: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 32)) (PreH2 : (retval_2 = (Znth (p_str_pos) (l) (0)))) (PreH3 : (retval = 0)) (PreH4 : (retval = 0)) (PreH5 : (p_str_pos < n)) (PreH6 : (0 <= start)) (PreH7 : (start <= p_str_pos)) (PreH8 : (p_str_pos <= n)) (PreH9 : (n <= INT_MAX)) (PreH10 : forall (i: Z) , (((start <= i) /\ (i < p_str_pos)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13)))) ,
  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_str_pos)
  **  (CharArray.full s n l )
  **  ((( &( "ch" ) )) # Char  |-> retval_2)
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (0 <= p_str_pos) ” 
  &&  “ (p_str_pos < n) ” 
  &&  “ (n <= INT_MAX) ”
.

Definition skip_whitespace_partial_solve_wit_4_aux := 
forall (p_pre: Z) (l: (@list Z)) (n: Z) (start: Z) (s: Z) (p_str_pos: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 32)) (PreH2 : (retval_2 = (Znth (p_str_pos) (l) (0)))) (PreH3 : (retval = 0)) (PreH4 : (retval = 0)) (PreH5 : (p_str_pos < n)) (PreH6 : (0 <= start)) (PreH7 : (start <= p_str_pos)) (PreH8 : (p_str_pos <= n)) (PreH9 : (n <= INT_MAX)) (PreH10 : forall (i: Z) , (((start <= i) /\ (i < p_str_pos)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13)))) ,
  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_str_pos)
  **  (CharArray.full s n l )
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
|--
  “ (0 <= p_str_pos) ” 
  &&  “ (p_str_pos < n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (retval_2 = 32) ” 
  &&  “ (retval_2 = (Znth (p_str_pos) (l) (0))) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (p_str_pos < n) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start <= p_str_pos) ” 
  &&  “ (p_str_pos <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ forall (i: Z) , (((start <= i) /\ (i < p_str_pos)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13))) ”
  &&  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_str_pos)
  **  (CharArray.full s n l )
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
.

Definition skip_whitespace_partial_solve_wit_4 := skip_whitespace_partial_solve_wit_4_pure -> skip_whitespace_partial_solve_wit_4_aux.

Definition skip_whitespace_partial_solve_wit_5_pure := 
forall (p_pre: Z) (l: (@list Z)) (n: Z) (start: Z) (s: Z) (p_str_pos: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 9)) (PreH2 : (retval_2 <> 32)) (PreH3 : (retval_2 = (Znth (p_str_pos) (l) (0)))) (PreH4 : (retval = 0)) (PreH5 : (retval = 0)) (PreH6 : (p_str_pos < n)) (PreH7 : (0 <= start)) (PreH8 : (start <= p_str_pos)) (PreH9 : (p_str_pos <= n)) (PreH10 : (n <= INT_MAX)) (PreH11 : forall (i: Z) , (((start <= i) /\ (i < p_str_pos)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13)))) ,
  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_str_pos)
  **  (CharArray.full s n l )
  **  ((( &( "ch" ) )) # Char  |-> retval_2)
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (0 <= p_str_pos) ” 
  &&  “ (p_str_pos < n) ” 
  &&  “ (n <= INT_MAX) ”
.

Definition skip_whitespace_partial_solve_wit_5_aux := 
forall (p_pre: Z) (l: (@list Z)) (n: Z) (start: Z) (s: Z) (p_str_pos: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 9)) (PreH2 : (retval_2 <> 32)) (PreH3 : (retval_2 = (Znth (p_str_pos) (l) (0)))) (PreH4 : (retval = 0)) (PreH5 : (retval = 0)) (PreH6 : (p_str_pos < n)) (PreH7 : (0 <= start)) (PreH8 : (start <= p_str_pos)) (PreH9 : (p_str_pos <= n)) (PreH10 : (n <= INT_MAX)) (PreH11 : forall (i: Z) , (((start <= i) /\ (i < p_str_pos)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13)))) ,
  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_str_pos)
  **  (CharArray.full s n l )
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
|--
  “ (0 <= p_str_pos) ” 
  &&  “ (p_str_pos < n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (retval_2 = 9) ” 
  &&  “ (retval_2 <> 32) ” 
  &&  “ (retval_2 = (Znth (p_str_pos) (l) (0))) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (p_str_pos < n) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start <= p_str_pos) ” 
  &&  “ (p_str_pos <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ forall (i: Z) , (((start <= i) /\ (i < p_str_pos)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13))) ”
  &&  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_str_pos)
  **  (CharArray.full s n l )
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
.

Definition skip_whitespace_partial_solve_wit_5 := skip_whitespace_partial_solve_wit_5_pure -> skip_whitespace_partial_solve_wit_5_aux.

Definition skip_whitespace_partial_solve_wit_6_pure := 
forall (p_pre: Z) (l: (@list Z)) (n: Z) (start: Z) (s: Z) (p_str_pos: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 13)) (PreH2 : (retval_2 <> 10)) (PreH3 : (retval_2 <> 9)) (PreH4 : (retval_2 <> 32)) (PreH5 : (retval_2 = (Znth (p_str_pos) (l) (0)))) (PreH6 : (retval = 0)) (PreH7 : (retval = 0)) (PreH8 : (p_str_pos < n)) (PreH9 : (0 <= start)) (PreH10 : (start <= p_str_pos)) (PreH11 : (p_str_pos <= n)) (PreH12 : (n <= INT_MAX)) (PreH13 : forall (i: Z) , (((start <= i) /\ (i < p_str_pos)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13)))) ,
  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_str_pos)
  **  (CharArray.full s n l )
  **  ((( &( "ch" ) )) # Char  |-> retval_2)
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (0 <= p_str_pos) ” 
  &&  “ (p_str_pos < n) ” 
  &&  “ (n <= INT_MAX) ”
.

Definition skip_whitespace_partial_solve_wit_6_aux := 
forall (p_pre: Z) (l: (@list Z)) (n: Z) (start: Z) (s: Z) (p_str_pos: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 13)) (PreH2 : (retval_2 <> 10)) (PreH3 : (retval_2 <> 9)) (PreH4 : (retval_2 <> 32)) (PreH5 : (retval_2 = (Znth (p_str_pos) (l) (0)))) (PreH6 : (retval = 0)) (PreH7 : (retval = 0)) (PreH8 : (p_str_pos < n)) (PreH9 : (0 <= start)) (PreH10 : (start <= p_str_pos)) (PreH11 : (p_str_pos <= n)) (PreH12 : (n <= INT_MAX)) (PreH13 : forall (i: Z) , (((start <= i) /\ (i < p_str_pos)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13)))) ,
  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_str_pos)
  **  (CharArray.full s n l )
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
|--
  “ (0 <= p_str_pos) ” 
  &&  “ (p_str_pos < n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (retval_2 = 13) ” 
  &&  “ (retval_2 <> 10) ” 
  &&  “ (retval_2 <> 9) ” 
  &&  “ (retval_2 <> 32) ” 
  &&  “ (retval_2 = (Znth (p_str_pos) (l) (0))) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (p_str_pos < n) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start <= p_str_pos) ” 
  &&  “ (p_str_pos <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ forall (i: Z) , (((start <= i) /\ (i < p_str_pos)) -> (((((Znth (i) (l) (0)) = 32) \/ ((Znth (i) (l) (0)) = 9)) \/ ((Znth (i) (l) (0)) = 10)) \/ ((Znth (i) (l) (0)) = 13))) ”
  &&  ((&((p_pre)  # "parser" ->ₛ "str")) # Ptr  |-> s)
  **  ((&((p_pre)  # "parser" ->ₛ "str_pos")) # Int  |-> p_str_pos)
  **  (CharArray.full s n l )
  **  ((&((p_pre)  # "parser" ->ₛ "str_len")) # Int  |-> n)
.

Definition skip_whitespace_partial_solve_wit_6 := skip_whitespace_partial_solve_wit_6_pure -> skip_whitespace_partial_solve_wit_6_aux.

(*----- Function parser_reset -----*)

(*----- Function parse_json -----*)

(*----- Function parse_element -----*)

(*----- Function parse_string -----*)

(*----- Function is_number_prefix -----*)

Definition is_number_prefix_safety_wit_1 := 
forall (ch_pre: Z) (PreH1 : ((-128) <= ch_pre)) (PreH2 : (ch_pre <= 255)) ,
  ((( &( "ch" ) )) # Char  |-> ch_pre)
|--
  “ (45 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 45) ”
.

Definition is_number_prefix_safety_wit_2 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 45)) (PreH2 : ((-128) <= ch_pre)) (PreH3 : (ch_pre <= 255)) ,
  ((( &( "ch" ) )) # Char  |-> ch_pre)
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition is_number_prefix_safety_wit_3 := 
forall (ch_pre: Z) (PreH1 : (ch_pre >= 48)) (PreH2 : (ch_pre <> 45)) (PreH3 : ((-128) <= ch_pre)) (PreH4 : (ch_pre <= 255)) ,
  ((( &( "ch" ) )) # Char  |-> ch_pre)
|--
  “ (57 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 57) ”
.

Definition is_number_prefix_return_wit_1 := 
forall (ch_pre: Z) (PreH1 : (ch_pre < 48)) (PreH2 : (ch_pre <> 45)) (PreH3 : ((-128) <= ch_pre)) (PreH4 : (ch_pre <= 255)) ,
  TT && emp 
|--
  “ (0 = 0) ” 
  &&  “ (ch_pre <> 45) ” 
  &&  “ (ch_pre < 48) ”
  &&  emp
.

Definition is_number_prefix_return_wit_2 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <= 57)) (PreH2 : (ch_pre >= 48)) (PreH3 : (ch_pre <> 45)) (PreH4 : ((-128) <= ch_pre)) (PreH5 : (ch_pre <= 255)) ,
  TT && emp 
|--
  “ (1 = 1) ” 
  &&  “ (48 <= ch_pre) ” 
  &&  “ (ch_pre <= 57) ”
  &&  emp
.

Definition is_number_prefix_return_wit_3 := 
forall (ch_pre: Z) (PreH1 : (ch_pre > 57)) (PreH2 : (ch_pre >= 48)) (PreH3 : (ch_pre <> 45)) (PreH4 : ((-128) <= ch_pre)) (PreH5 : (ch_pre <= 255)) ,
  TT && emp 
|--
  “ (0 = 0) ” 
  &&  “ (ch_pre <> 45) ” 
  &&  “ (57 < ch_pre) ”
  &&  emp
.

Definition is_number_prefix_return_wit_4 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 45)) (PreH2 : ((-128) <= ch_pre)) (PreH3 : (ch_pre <= 255)) ,
  TT && emp 
|--
  “ (1 = 1) ” 
  &&  “ (ch_pre = 45) ”
  &&  emp
.

(*----- Function parse_number -----*)

(*----- Function parse_literal -----*)

(*----- Function find_and_skip -----*)

(*----- Function parse_object -----*)

(*----- Function parse_array -----*)

(*----- Function is_hex -----*)

Definition is_hex_safety_wit_1 := 
forall (ch_pre: Z) (PreH1 : ((-128) <= ch_pre)) (PreH2 : (ch_pre <= 255)) ,
  ((( &( "ch" ) )) # Char  |-> ch_pre)
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition is_hex_safety_wit_2 := 
forall (ch_pre: Z) (PreH1 : (ch_pre >= 48)) (PreH2 : ((-128) <= ch_pre)) (PreH3 : (ch_pre <= 255)) ,
  ((( &( "ch" ) )) # Char  |-> ch_pre)
|--
  “ (57 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 57) ”
.

Definition is_hex_safety_wit_3 := 
forall (ch_pre: Z) (PreH1 : (ch_pre > 57)) (PreH2 : (ch_pre >= 48)) (PreH3 : ((-128) <= ch_pre)) (PreH4 : (ch_pre <= 255)) ,
  ((( &( "ch" ) )) # Char  |-> ch_pre)
|--
  “ (65 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65) ”
.

Definition is_hex_safety_wit_4 := 
forall (ch_pre: Z) (PreH1 : (ch_pre < 48)) (PreH2 : ((-128) <= ch_pre)) (PreH3 : (ch_pre <= 255)) ,
  ((( &( "ch" ) )) # Char  |-> ch_pre)
|--
  “ (65 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65) ”
.

Definition is_hex_safety_wit_5 := 
forall (ch_pre: Z) (PreH1 : (ch_pre >= 65)) (PreH2 : (ch_pre < 48)) (PreH3 : ((-128) <= ch_pre)) (PreH4 : (ch_pre <= 255)) ,
  ((( &( "ch" ) )) # Char  |-> ch_pre)
|--
  “ False ”
.

Definition is_hex_safety_wit_6 := 
forall (ch_pre: Z) (PreH1 : (ch_pre >= 65)) (PreH2 : (ch_pre > 57)) (PreH3 : (ch_pre >= 48)) (PreH4 : ((-128) <= ch_pre)) (PreH5 : (ch_pre <= 255)) ,
  ((( &( "ch" ) )) # Char  |-> ch_pre)
|--
  “ (70 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 70) ”
.

Definition is_hex_safety_wit_7 := 
forall (ch_pre: Z) (PreH1 : (ch_pre < 65)) (PreH2 : (ch_pre < 48)) (PreH3 : ((-128) <= ch_pre)) (PreH4 : (ch_pre <= 255)) ,
  ((( &( "ch" ) )) # Char  |-> ch_pre)
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition is_hex_safety_wit_8 := 
forall (ch_pre: Z) (PreH1 : (ch_pre < 65)) (PreH2 : (ch_pre > 57)) (PreH3 : (ch_pre >= 48)) (PreH4 : ((-128) <= ch_pre)) (PreH5 : (ch_pre <= 255)) ,
  ((( &( "ch" ) )) # Char  |-> ch_pre)
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition is_hex_safety_wit_9 := 
forall (ch_pre: Z) (PreH1 : (ch_pre > 70)) (PreH2 : (ch_pre >= 65)) (PreH3 : (ch_pre > 57)) (PreH4 : (ch_pre >= 48)) (PreH5 : ((-128) <= ch_pre)) (PreH6 : (ch_pre <= 255)) ,
  ((( &( "ch" ) )) # Char  |-> ch_pre)
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition is_hex_safety_wit_10 := 
forall (ch_pre: Z) (PreH1 : (ch_pre >= 97)) (PreH2 : (ch_pre < 65)) (PreH3 : (ch_pre < 48)) (PreH4 : ((-128) <= ch_pre)) (PreH5 : (ch_pre <= 255)) ,
  ((( &( "ch" ) )) # Char  |-> ch_pre)
|--
  “ False ”
.

Definition is_hex_safety_wit_11 := 
forall (ch_pre: Z) (PreH1 : (ch_pre >= 97)) (PreH2 : (ch_pre < 65)) (PreH3 : (ch_pre > 57)) (PreH4 : (ch_pre >= 48)) (PreH5 : ((-128) <= ch_pre)) (PreH6 : (ch_pre <= 255)) ,
  ((( &( "ch" ) )) # Char  |-> ch_pre)
|--
  “ False ”
.

Definition is_hex_safety_wit_12 := 
forall (ch_pre: Z) (PreH1 : (ch_pre >= 97)) (PreH2 : (ch_pre > 70)) (PreH3 : (ch_pre >= 65)) (PreH4 : (ch_pre > 57)) (PreH5 : (ch_pre >= 48)) (PreH6 : ((-128) <= ch_pre)) (PreH7 : (ch_pre <= 255)) ,
  ((( &( "ch" ) )) # Char  |-> ch_pre)
|--
  “ (102 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 102) ”
.

Definition is_hex_return_wit_1 := 
forall (ch_pre: Z) (PreH1 : (ch_pre < 97)) (PreH2 : (ch_pre > 70)) (PreH3 : (ch_pre >= 65)) (PreH4 : (ch_pre > 57)) (PreH5 : (ch_pre >= 48)) (PreH6 : ((-128) <= ch_pre)) (PreH7 : (ch_pre <= 255)) ,
  TT && emp 
|--
  “ (0 = 0) ” 
  &&  “ (57 < ch_pre) ” 
  &&  “ (70 < ch_pre) ” 
  &&  “ (ch_pre < 97) ”
  &&  emp
.

Definition is_hex_return_wit_2 := 
forall (ch_pre: Z) (PreH1 : (ch_pre < 97)) (PreH2 : (ch_pre < 65)) (PreH3 : (ch_pre > 57)) (PreH4 : (ch_pre >= 48)) (PreH5 : ((-128) <= ch_pre)) (PreH6 : (ch_pre <= 255)) ,
  TT && emp 
|--
  “ (0 = 0) ” 
  &&  “ (57 < ch_pre) ” 
  &&  “ (ch_pre < 65) ” 
  &&  “ (ch_pre < 97) ”
  &&  emp
.

Definition is_hex_return_wit_3 := 
forall (ch_pre: Z) (PreH1 : (ch_pre < 97)) (PreH2 : (ch_pre < 65)) (PreH3 : (ch_pre < 48)) (PreH4 : ((-128) <= ch_pre)) (PreH5 : (ch_pre <= 255)) ,
  TT && emp 
|--
  “ (0 = 0) ” 
  &&  “ (ch_pre < 48) ” 
  &&  “ (ch_pre < 65) ” 
  &&  “ (ch_pre < 97) ”
  &&  emp
.

Definition is_hex_return_wit_4 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <= 102)) (PreH2 : (ch_pre >= 97)) (PreH3 : (ch_pre > 70)) (PreH4 : (ch_pre >= 65)) (PreH5 : (ch_pre > 57)) (PreH6 : (ch_pre >= 48)) (PreH7 : ((-128) <= ch_pre)) (PreH8 : (ch_pre <= 255)) ,
  TT && emp 
|--
  “ (1 = 1) ” 
  &&  “ (97 <= ch_pre) ” 
  &&  “ (ch_pre <= 102) ”
  &&  emp
.

Definition is_hex_return_wit_5 := 
forall (ch_pre: Z) (PreH1 : (ch_pre > 102)) (PreH2 : (ch_pre >= 97)) (PreH3 : (ch_pre > 70)) (PreH4 : (ch_pre >= 65)) (PreH5 : (ch_pre > 57)) (PreH6 : (ch_pre >= 48)) (PreH7 : ((-128) <= ch_pre)) (PreH8 : (ch_pre <= 255)) ,
  TT && emp 
|--
  “ (0 = 0) ” 
  &&  “ (57 < ch_pre) ” 
  &&  “ (70 < ch_pre) ” 
  &&  “ (102 < ch_pre) ”
  &&  emp
.

Definition is_hex_return_wit_6 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <= 57)) (PreH2 : (ch_pre >= 48)) (PreH3 : ((-128) <= ch_pre)) (PreH4 : (ch_pre <= 255)) ,
  TT && emp 
|--
  “ (1 = 1) ” 
  &&  “ (48 <= ch_pre) ” 
  &&  “ (ch_pre <= 57) ”
  &&  emp
.

Definition is_hex_return_wit_7 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <= 70)) (PreH2 : (ch_pre >= 65)) (PreH3 : (ch_pre > 57)) (PreH4 : (ch_pre >= 48)) (PreH5 : ((-128) <= ch_pre)) (PreH6 : (ch_pre <= 255)) ,
  TT && emp 
|--
  “ (1 = 1) ” 
  &&  “ (65 <= ch_pre) ” 
  &&  “ (ch_pre <= 70) ”
  &&  emp
.

(*----- Function alloc_token -----*)

(*----- Function init_token -----*)

(*----- Function finalize_token -----*)

(*----- Function set_token_string -----*)

Definition set_token_string_return_wit_1 := 
forall (string_pre: Z) (token_pre: Z) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "str")) # Ptr  |-> string_pre)
|--
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "str")) # Ptr  |-> string_pre)
.

(*----- Function get_token_string -----*)

Definition get_token_string_return_wit_1 := 
forall (token_pre: Z) (s: Z) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "str")) # Ptr  |-> s)
|--
  “ (s = s) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "str")) # Ptr  |-> s)
.

(*----- Function set_token_string_length -----*)

Definition set_token_string_length_safety_wit_1 := 
forall (string_length_pre: Z) (token_pre: Z) (w: Z) (PreH1 : (0 <= w)) (PreH2 : (w <= UINT_MAX)) (PreH3 : (INT_MIN <= string_length_pre)) (PreH4 : (string_length_pre <= INT_MAX)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
  **  ((( &( "string_length" ) )) # Int  |-> string_length_pre)
  **  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (0 <= 31) ” 
  &&  “ (0 <= 0) ”
.

Definition set_token_string_length_safety_wit_2 := 
forall (string_length_pre: Z) (token_pre: Z) (w: Z) (PreH1 : (0 <= w)) (PreH2 : (w <= UINT_MAX)) (PreH3 : (INT_MIN <= string_length_pre)) (PreH4 : (string_length_pre <= INT_MAX)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
  **  ((( &( "string_length" ) )) # Int  |-> string_length_pre)
  **  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition set_token_string_length_return_wit_1 := 
(
forall (string_length_pre: Z) (token_pre: Z) (w: Z) (PreH1 : (0 <= w)) (PreH2 : (w <= UINT_MAX)) (PreH3 : (INT_MIN <= string_length_pre)) (PreH4 : (string_length_pre <= INT_MAX)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> (Z.lor (Z.land w 4294901760) (unsigned_last_nbits ((Z.shiftl (Z.land string_length_pre 65535) 0)) (32))))
|--
  EX (token_pre_packed_fields: Z) ,
  “ (token_pre_packed_fields = (Z.lor (Z.land w 4294901760) (Z.shiftl (Z.land string_length_pre 65535) 0))) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> token_pre_packed_fields)
) \/
(
forall (string_length_pre: Z) (w: Z) (PreH1 : (0 <= w)) (PreH2 : (w <= UINT_MAX)) (PreH3 : (INT_MIN <= string_length_pre)) (PreH4 : (string_length_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Z.lor (Z.land w 4294901760) (unsigned_last_nbits ((Z.shiftl (Z.land string_length_pre 65535) 0)) (32))) = (Z.lor (Z.land w 4294901760) (Z.shiftl (Z.land string_length_pre 65535) 0))) ” 
  &&  “ ((Z.lor (Z.land w 4294901760) (unsigned_last_nbits ((Z.shiftl (Z.land string_length_pre 65535) 0)) (32))) = (Z.lor (Z.land w 4294901760) (Z.shiftl (Z.land string_length_pre 65535) 0))) ”
  &&  emp
).

Definition set_token_string_length_return_wit_1_split_goal_1 := 
forall (string_length_pre: Z) (w: Z) (PreH1 : (0 <= w)) (PreH2 : (w <= UINT_MAX)) (PreH3 : (INT_MIN <= string_length_pre)) (PreH4 : (string_length_pre <= INT_MAX)) ,
  ((Z.lor (Z.land w 4294901760) (unsigned_last_nbits ((Z.shiftl (Z.land string_length_pre 65535) 0)) (32))) = (Z.lor (Z.land w 4294901760) (Z.shiftl (Z.land string_length_pre 65535) 0)))
.

Definition set_token_string_length_return_wit_1_split_goal_2 := 
forall (string_length_pre: Z) (w: Z) (PreH1 : (0 <= w)) (PreH2 : (w <= UINT_MAX)) (PreH3 : (INT_MIN <= string_length_pre)) (PreH4 : (string_length_pre <= INT_MAX)) ,
  ((Z.lor (Z.land w 4294901760) (unsigned_last_nbits ((Z.shiftl (Z.land string_length_pre 65535) 0)) (32))) = (Z.lor (Z.land w 4294901760) (Z.shiftl (Z.land string_length_pre 65535) 0)))
.

(*----- Function set_token_type -----*)

Definition set_token_type_safety_wit_1 := 
forall (token_type_pre: Z) (token_pre: Z) (w: Z) (PreH1 : (0 <= w)) (PreH2 : (w <= UINT_MAX)) (PreH3 : (INT_MIN <= token_type_pre)) (PreH4 : (token_type_pre <= INT_MAX)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
  **  ((( &( "token_type" ) )) # Int  |-> token_type_pre)
  **  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (16 <= 31) ” 
  &&  “ (0 <= 16) ”
.

Definition set_token_type_safety_wit_2 := 
forall (token_type_pre: Z) (token_pre: Z) (w: Z) (PreH1 : (0 <= w)) (PreH2 : (w <= UINT_MAX)) (PreH3 : (INT_MIN <= token_type_pre)) (PreH4 : (token_type_pre <= INT_MAX)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
  **  ((( &( "token_type" ) )) # Int  |-> token_type_pre)
  **  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (16 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 16) ”
.

Definition set_token_type_return_wit_1 := 
(
forall (token_type_pre: Z) (token_pre: Z) (w: Z) (PreH1 : (0 <= w)) (PreH2 : (w <= UINT_MAX)) (PreH3 : (INT_MIN <= token_type_pre)) (PreH4 : (token_type_pre <= INT_MAX)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> (Z.lor (Z.land w 4293984255) (unsigned_last_nbits ((Z.shiftl (Z.land token_type_pre 15) 16)) (32))))
|--
  EX (token_pre_packed_fields: Z) ,
  “ (token_pre_packed_fields = (Z.lor (Z.land w 4293984255) (Z.shiftl (Z.land token_type_pre 15) 16))) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> token_pre_packed_fields)
) \/
(
forall (token_type_pre: Z) (w: Z) (PreH1 : (0 <= w)) (PreH2 : (w <= UINT_MAX)) (PreH3 : (INT_MIN <= token_type_pre)) (PreH4 : (token_type_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Z.lor (Z.land w 4293984255) (unsigned_last_nbits ((Z.shiftl (Z.land token_type_pre 15) 16)) (32))) = (Z.lor (Z.land w 4293984255) (Z.shiftl (Z.land token_type_pre 15) 16))) ” 
  &&  “ ((Z.lor (Z.land w 4293984255) (unsigned_last_nbits ((Z.shiftl (Z.land token_type_pre 15) 16)) (32))) = (Z.lor (Z.land w 4293984255) (Z.shiftl (Z.land token_type_pre 15) 16))) ”
  &&  emp
).

Definition set_token_type_return_wit_1_split_goal_1 := 
forall (token_type_pre: Z) (w: Z) (PreH1 : (0 <= w)) (PreH2 : (w <= UINT_MAX)) (PreH3 : (INT_MIN <= token_type_pre)) (PreH4 : (token_type_pre <= INT_MAX)) ,
  ((Z.lor (Z.land w 4293984255) (unsigned_last_nbits ((Z.shiftl (Z.land token_type_pre 15) 16)) (32))) = (Z.lor (Z.land w 4293984255) (Z.shiftl (Z.land token_type_pre 15) 16)))
.

Definition set_token_type_return_wit_1_split_goal_2 := 
forall (token_type_pre: Z) (w: Z) (PreH1 : (0 <= w)) (PreH2 : (w <= UINT_MAX)) (PreH3 : (INT_MIN <= token_type_pre)) (PreH4 : (token_type_pre <= INT_MAX)) ,
  ((Z.lor (Z.land w 4293984255) (unsigned_last_nbits ((Z.shiftl (Z.land token_type_pre 15) 16)) (32))) = (Z.lor (Z.land w 4293984255) (Z.shiftl (Z.land token_type_pre 15) 16)))
.

(*----- Function set_token_level -----*)

Definition set_token_level_safety_wit_1 := 
forall (level_pre: Z) (token_pre: Z) (w: Z) (PreH1 : (0 <= w)) (PreH2 : (w <= UINT_MAX)) (PreH3 : (INT_MIN <= level_pre)) (PreH4 : (level_pre <= INT_MAX)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
  **  ((( &( "level" ) )) # Int  |-> level_pre)
  **  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (20 <= 31) ” 
  &&  “ (0 <= 20) ”
.

Definition set_token_level_safety_wit_2 := 
forall (level_pre: Z) (token_pre: Z) (w: Z) (PreH1 : (0 <= w)) (PreH2 : (w <= UINT_MAX)) (PreH3 : (INT_MIN <= level_pre)) (PreH4 : (level_pre <= INT_MAX)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
  **  ((( &( "level" ) )) # Int  |-> level_pre)
  **  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (20 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 20) ”
.

Definition set_token_level_return_wit_1 := 
(
forall (level_pre: Z) (token_pre: Z) (w: Z) (PreH1 : (0 <= w)) (PreH2 : (w <= UINT_MAX)) (PreH3 : (INT_MIN <= level_pre)) (PreH4 : (level_pre <= INT_MAX)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> (Z.lor (Z.land w 2148532223) (unsigned_last_nbits ((Z.shiftl (Z.land level_pre 2047) 20)) (32))))
|--
  EX (token_pre_packed_fields: Z) ,
  “ (token_pre_packed_fields = (Z.lor (Z.land w 2148532223) (Z.shiftl (Z.land level_pre 2047) 20))) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> token_pre_packed_fields)
) \/
(
forall (level_pre: Z) (w: Z) (PreH1 : (0 <= w)) (PreH2 : (w <= UINT_MAX)) (PreH3 : (INT_MIN <= level_pre)) (PreH4 : (level_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Z.lor (Z.land w 2148532223) (unsigned_last_nbits ((Z.shiftl (Z.land level_pre 2047) 20)) (32))) = (Z.lor (Z.land w 2148532223) (Z.shiftl (Z.land level_pre 2047) 20))) ” 
  &&  “ ((Z.lor (Z.land w 2148532223) (unsigned_last_nbits ((Z.shiftl (Z.land level_pre 2047) 20)) (32))) = (Z.lor (Z.land w 2148532223) (Z.shiftl (Z.land level_pre 2047) 20))) ”
  &&  emp
).

Definition set_token_level_return_wit_1_split_goal_1 := 
forall (level_pre: Z) (w: Z) (PreH1 : (0 <= w)) (PreH2 : (w <= UINT_MAX)) (PreH3 : (INT_MIN <= level_pre)) (PreH4 : (level_pre <= INT_MAX)) ,
  ((Z.lor (Z.land w 2148532223) (unsigned_last_nbits ((Z.shiftl (Z.land level_pre 2047) 20)) (32))) = (Z.lor (Z.land w 2148532223) (Z.shiftl (Z.land level_pre 2047) 20)))
.

Definition set_token_level_return_wit_1_split_goal_2 := 
forall (level_pre: Z) (w: Z) (PreH1 : (0 <= w)) (PreH2 : (w <= UINT_MAX)) (PreH3 : (INT_MIN <= level_pre)) (PreH4 : (level_pre <= INT_MAX)) ,
  ((Z.lor (Z.land w 2148532223) (unsigned_last_nbits ((Z.shiftl (Z.land level_pre 2047) 20)) (32))) = (Z.lor (Z.land w 2148532223) (Z.shiftl (Z.land level_pre 2047) 20)))
.

(*----- Function set_token_is_last -----*)

Definition set_token_is_last_safety_wit_1 := 
forall (is_last_pre: Z) (token_pre: Z) (w: Z) (PreH1 : (0 <= w)) (PreH2 : (w <= UINT_MAX)) (PreH3 : (0 <= is_last_pre)) (PreH4 : (is_last_pre <= 1)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
  **  ((( &( "is_last" ) )) # Bool  |-> is_last_pre)
  **  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (31 <= 31) ” 
  &&  “ (0 <= 31) ”
.

Definition set_token_is_last_safety_wit_2 := 
forall (is_last_pre: Z) (token_pre: Z) (w: Z) (PreH1 : (0 <= w)) (PreH2 : (w <= UINT_MAX)) (PreH3 : (0 <= is_last_pre)) (PreH4 : (is_last_pre <= 1)) ,
  ((( &( "token" ) )) # Ptr  |-> token_pre)
  **  ((( &( "is_last" ) )) # Bool  |-> is_last_pre)
  **  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> w)
|--
  “ (31 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 31) ”
.

Definition set_token_is_last_return_wit_1 := 
(
forall (is_last_pre: Z) (token_pre: Z) (w: Z) (PreH1 : (0 <= w)) (PreH2 : (w <= UINT_MAX)) (PreH3 : (0 <= is_last_pre)) (PreH4 : (is_last_pre <= 1)) ,
  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> (Z.lor (Z.land w INT_MAX) (unsigned_last_nbits ((Z.shiftl (Z.land is_last_pre 1) 31)) (32))))
|--
  EX (token_pre_packed_fields: Z) ,
  “ (token_pre_packed_fields = (Z.lor (Z.land w INT_MAX) (Z.shiftl (Z.land is_last_pre 1) 31))) ”
  &&  ((&((token_pre)  # "anonymous struct 1" ->ₛ "packed_fields")) # UInt  |-> token_pre_packed_fields)
) \/
(
forall (is_last_pre: Z) (w: Z) (PreH1 : (0 <= w)) (PreH2 : (w <= UINT_MAX)) (PreH3 : (0 <= is_last_pre)) (PreH4 : (is_last_pre <= 1)) ,
  TT && emp 
|--
  “ ((Z.lor (Z.land w INT_MAX) (unsigned_last_nbits ((Z.shiftl (Z.land is_last_pre 1) 31)) (32))) = (Z.lor (Z.land w INT_MAX) (Z.shiftl (Z.land is_last_pre 1) 31))) ” 
  &&  “ ((Z.lor (Z.land w INT_MAX) (unsigned_last_nbits ((Z.shiftl (Z.land is_last_pre 1) 31)) (32))) = (Z.lor (Z.land w INT_MAX) (Z.shiftl (Z.land is_last_pre 1) 31))) ”
  &&  emp
).

Definition set_token_is_last_return_wit_1_split_goal_1 := 
forall (is_last_pre: Z) (w: Z) (PreH1 : (0 <= w)) (PreH2 : (w <= UINT_MAX)) (PreH3 : (0 <= is_last_pre)) (PreH4 : (is_last_pre <= 1)) ,
  ((Z.lor (Z.land w INT_MAX) (unsigned_last_nbits ((Z.shiftl (Z.land is_last_pre 1) 31)) (32))) = (Z.lor (Z.land w INT_MAX) (Z.shiftl (Z.land is_last_pre 1) 31)))
.

Definition set_token_is_last_return_wit_1_split_goal_2 := 
forall (is_last_pre: Z) (w: Z) (PreH1 : (0 <= w)) (PreH2 : (w <= UINT_MAX)) (PreH3 : (0 <= is_last_pre)) (PreH4 : (is_last_pre <= 1)) ,
  ((Z.lor (Z.land w INT_MAX) (unsigned_last_nbits ((Z.shiftl (Z.land is_last_pre 1) 31)) (32))) = (Z.lor (Z.land w INT_MAX) (Z.shiftl (Z.land is_last_pre 1) 31)))
.

(*----- Function token_type_name -----*)

(*----- Function log_input_state -----*)

(*----- Function find_sibling -----*)

Module Type VC_Correct.


Axiom proof_of_at_eos_return_wit_1 : at_eos_return_wit_1.
Axiom proof_of_at_eos_return_wit_2 : at_eos_return_wit_2.
Axiom proof_of_peek_char_return_wit_1 : peek_char_return_wit_1.
Axiom proof_of_peek_char_partial_solve_wit_1 : peek_char_partial_solve_wit_1.
Axiom proof_of_get_char_safety_wit_1 : get_char_safety_wit_1.
Axiom proof_of_get_char_safety_wit_2 : get_char_safety_wit_2.
Axiom proof_of_get_char_return_wit_1 : get_char_return_wit_1.
Axiom proof_of_get_char_partial_solve_wit_1 : get_char_partial_solve_wit_1.
Axiom proof_of_ref_char_return_wit_1 : ref_char_return_wit_1.
Axiom proof_of_is_digit_safety_wit_1 : is_digit_safety_wit_1.
Axiom proof_of_is_digit_safety_wit_2 : is_digit_safety_wit_2.
Axiom proof_of_is_digit_return_wit_1 : is_digit_return_wit_1.
Axiom proof_of_is_digit_return_wit_2 : is_digit_return_wit_2.
Axiom proof_of_is_digit_return_wit_3 : is_digit_return_wit_3.
Axiom proof_of_token_is_null_safety_wit_1 : token_is_null_safety_wit_1.
Axiom proof_of_token_is_null_return_wit_1 : token_is_null_return_wit_1.
Axiom proof_of_token_is_null_return_wit_2 : token_is_null_return_wit_2.
Axiom proof_of_token_is_first_safety_wit_1 : token_is_first_safety_wit_1.
Axiom proof_of_token_is_first_safety_wit_2 : token_is_first_safety_wit_2.
Axiom proof_of_token_is_first_safety_wit_3 : token_is_first_safety_wit_3.
Axiom proof_of_token_is_first_return_wit_1 : token_is_first_return_wit_1.
Axiom proof_of_token_is_first_return_wit_2 : token_is_first_return_wit_2.
Axiom proof_of_token_is_last_safety_wit_1 : token_is_last_safety_wit_1.
Axiom proof_of_token_is_last_safety_wit_2 : token_is_last_safety_wit_2.
Axiom proof_of_token_is_last_return_wit_1 : token_is_last_return_wit_1.
Axiom proof_of_token_is_last_return_wit_2 : token_is_last_return_wit_2.
Axiom proof_of_mu_json_token_string_safety_wit_1 : mu_json_token_string_safety_wit_1.
Axiom proof_of_mu_json_token_string_safety_wit_2 : mu_json_token_string_safety_wit_2.
Axiom proof_of_mu_json_token_string_safety_wit_3 : mu_json_token_string_safety_wit_3.
Axiom proof_of_mu_json_token_string_safety_wit_4 : mu_json_token_string_safety_wit_4.
Axiom proof_of_mu_json_token_string_safety_wit_5 : mu_json_token_string_safety_wit_5.
Axiom proof_of_mu_json_token_string_entail_wit_1_1 : mu_json_token_string_entail_wit_1_1.
Axiom proof_of_mu_json_token_string_entail_wit_1_2 : mu_json_token_string_entail_wit_1_2.
Axiom proof_of_mu_json_token_string_entail_wit_2_1 : mu_json_token_string_entail_wit_2_1.
Axiom proof_of_mu_json_token_string_entail_wit_2_2 : mu_json_token_string_entail_wit_2_2.
Axiom proof_of_mu_json_token_string_return_wit_1 : mu_json_token_string_return_wit_1.
Axiom proof_of_mu_json_token_string_return_wit_2 : mu_json_token_string_return_wit_2.
Axiom proof_of_mu_json_token_string_partial_solve_wit_1 : mu_json_token_string_partial_solve_wit_1.
Axiom proof_of_mu_json_token_string_partial_solve_wit_2 : mu_json_token_string_partial_solve_wit_2.
Axiom proof_of_mu_json_token_string_length_safety_wit_1 : mu_json_token_string_length_safety_wit_1.
Axiom proof_of_mu_json_token_string_length_safety_wit_2 : mu_json_token_string_length_safety_wit_2.
Axiom proof_of_mu_json_token_string_length_safety_wit_3 : mu_json_token_string_length_safety_wit_3.
Axiom proof_of_mu_json_token_string_length_safety_wit_4 : mu_json_token_string_length_safety_wit_4.
Axiom proof_of_mu_json_token_string_length_safety_wit_5 : mu_json_token_string_length_safety_wit_5.
Axiom proof_of_mu_json_token_string_length_safety_wit_6 : mu_json_token_string_length_safety_wit_6.
Axiom proof_of_mu_json_token_string_length_safety_wit_7 : mu_json_token_string_length_safety_wit_7.
Axiom proof_of_mu_json_token_string_length_safety_wit_8 : mu_json_token_string_length_safety_wit_8.
Axiom proof_of_mu_json_token_string_length_entail_wit_1_1 : mu_json_token_string_length_entail_wit_1_1.
Axiom proof_of_mu_json_token_string_length_entail_wit_1_2 : mu_json_token_string_length_entail_wit_1_2.
Axiom proof_of_mu_json_token_string_length_entail_wit_2_1 : mu_json_token_string_length_entail_wit_2_1.
Axiom proof_of_mu_json_token_string_length_entail_wit_2_2 : mu_json_token_string_length_entail_wit_2_2.
Axiom proof_of_mu_json_token_string_length_return_wit_1 : mu_json_token_string_length_return_wit_1.
Axiom proof_of_mu_json_token_string_length_return_wit_2 : mu_json_token_string_length_return_wit_2.
Axiom proof_of_mu_json_token_string_length_partial_solve_wit_1 : mu_json_token_string_length_partial_solve_wit_1.
Axiom proof_of_mu_json_token_string_length_partial_solve_wit_2 : mu_json_token_string_length_partial_solve_wit_2.
Axiom proof_of_mu_json_token_type_safety_wit_1 : mu_json_token_type_safety_wit_1.
Axiom proof_of_mu_json_token_type_safety_wit_2 : mu_json_token_type_safety_wit_2.
Axiom proof_of_mu_json_token_type_safety_wit_3 : mu_json_token_type_safety_wit_3.
Axiom proof_of_mu_json_token_type_safety_wit_4 : mu_json_token_type_safety_wit_4.
Axiom proof_of_mu_json_token_type_safety_wit_5 : mu_json_token_type_safety_wit_5.
Axiom proof_of_mu_json_token_type_safety_wit_6 : mu_json_token_type_safety_wit_6.
Axiom proof_of_mu_json_token_type_safety_wit_7 : mu_json_token_type_safety_wit_7.
Axiom proof_of_mu_json_token_type_entail_wit_1_1 : mu_json_token_type_entail_wit_1_1.
Axiom proof_of_mu_json_token_type_entail_wit_1_2 : mu_json_token_type_entail_wit_1_2.
Axiom proof_of_mu_json_token_type_entail_wit_2_1 : mu_json_token_type_entail_wit_2_1.
Axiom proof_of_mu_json_token_type_entail_wit_2_2 : mu_json_token_type_entail_wit_2_2.
Axiom proof_of_mu_json_token_type_return_wit_1 : mu_json_token_type_return_wit_1.
Axiom proof_of_mu_json_token_type_return_wit_2 : mu_json_token_type_return_wit_2.
Axiom proof_of_mu_json_token_type_partial_solve_wit_1 : mu_json_token_type_partial_solve_wit_1.
Axiom proof_of_mu_json_token_type_partial_solve_wit_2 : mu_json_token_type_partial_solve_wit_2.
Axiom proof_of_mu_json_token_level_safety_wit_1 : mu_json_token_level_safety_wit_1.
Axiom proof_of_mu_json_token_level_safety_wit_2 : mu_json_token_level_safety_wit_2.
Axiom proof_of_mu_json_token_level_safety_wit_3 : mu_json_token_level_safety_wit_3.
Axiom proof_of_mu_json_token_level_safety_wit_4 : mu_json_token_level_safety_wit_4.
Axiom proof_of_mu_json_token_level_safety_wit_5 : mu_json_token_level_safety_wit_5.
Axiom proof_of_mu_json_token_level_safety_wit_6 : mu_json_token_level_safety_wit_6.
Axiom proof_of_mu_json_token_level_safety_wit_7 : mu_json_token_level_safety_wit_7.
Axiom proof_of_mu_json_token_level_safety_wit_8 : mu_json_token_level_safety_wit_8.
Axiom proof_of_mu_json_token_level_entail_wit_1_1 : mu_json_token_level_entail_wit_1_1.
Axiom proof_of_mu_json_token_level_entail_wit_1_2 : mu_json_token_level_entail_wit_1_2.
Axiom proof_of_mu_json_token_level_entail_wit_2_1 : mu_json_token_level_entail_wit_2_1.
Axiom proof_of_mu_json_token_level_entail_wit_2_2 : mu_json_token_level_entail_wit_2_2.
Axiom proof_of_mu_json_token_level_return_wit_1 : mu_json_token_level_return_wit_1.
Axiom proof_of_mu_json_token_level_return_wit_2 : mu_json_token_level_return_wit_2.
Axiom proof_of_mu_json_token_level_partial_solve_wit_1 : mu_json_token_level_partial_solve_wit_1.
Axiom proof_of_mu_json_token_level_partial_solve_wit_2 : mu_json_token_level_partial_solve_wit_2.
Axiom proof_of_mu_json_token_is_first_safety_wit_1 : mu_json_token_is_first_safety_wit_1.
Axiom proof_of_mu_json_token_is_first_safety_wit_2 : mu_json_token_is_first_safety_wit_2.
Axiom proof_of_mu_json_token_is_first_safety_wit_3 : mu_json_token_is_first_safety_wit_3.
Axiom proof_of_mu_json_token_is_first_safety_wit_4 : mu_json_token_is_first_safety_wit_4.
Axiom proof_of_mu_json_token_is_first_safety_wit_5 : mu_json_token_is_first_safety_wit_5.
Axiom proof_of_mu_json_token_is_first_entail_wit_1_1 : mu_json_token_is_first_entail_wit_1_1.
Axiom proof_of_mu_json_token_is_first_entail_wit_1_2 : mu_json_token_is_first_entail_wit_1_2.
Axiom proof_of_mu_json_token_is_first_entail_wit_2_1 : mu_json_token_is_first_entail_wit_2_1.
Axiom proof_of_mu_json_token_is_first_entail_wit_2_2 : mu_json_token_is_first_entail_wit_2_2.
Axiom proof_of_mu_json_token_is_first_return_wit_1 : mu_json_token_is_first_return_wit_1.
Axiom proof_of_mu_json_token_is_first_return_wit_2 : mu_json_token_is_first_return_wit_2.
Axiom proof_of_mu_json_token_is_first_return_wit_3 : mu_json_token_is_first_return_wit_3.
Axiom proof_of_mu_json_token_is_first_partial_solve_wit_1 : mu_json_token_is_first_partial_solve_wit_1.
Axiom proof_of_mu_json_token_is_first_partial_solve_wit_2 : mu_json_token_is_first_partial_solve_wit_2.
Axiom proof_of_mu_json_token_is_first_partial_solve_wit_3_pure : mu_json_token_is_first_partial_solve_wit_3_pure.
Axiom proof_of_mu_json_token_is_first_partial_solve_wit_3 : mu_json_token_is_first_partial_solve_wit_3.
Axiom proof_of_mu_json_token_is_last_safety_wit_1 : mu_json_token_is_last_safety_wit_1.
Axiom proof_of_mu_json_token_is_last_safety_wit_2 : mu_json_token_is_last_safety_wit_2.
Axiom proof_of_mu_json_token_is_last_safety_wit_3 : mu_json_token_is_last_safety_wit_3.
Axiom proof_of_mu_json_token_is_last_safety_wit_4 : mu_json_token_is_last_safety_wit_4.
Axiom proof_of_mu_json_token_is_last_safety_wit_5 : mu_json_token_is_last_safety_wit_5.
Axiom proof_of_mu_json_token_is_last_entail_wit_1_1 : mu_json_token_is_last_entail_wit_1_1.
Axiom proof_of_mu_json_token_is_last_entail_wit_1_2 : mu_json_token_is_last_entail_wit_1_2.
Axiom proof_of_mu_json_token_is_last_entail_wit_2_1 : mu_json_token_is_last_entail_wit_2_1.
Axiom proof_of_mu_json_token_is_last_entail_wit_2_2 : mu_json_token_is_last_entail_wit_2_2.
Axiom proof_of_mu_json_token_is_last_return_wit_1 : mu_json_token_is_last_return_wit_1.
Axiom proof_of_mu_json_token_is_last_return_wit_2 : mu_json_token_is_last_return_wit_2.
Axiom proof_of_mu_json_token_is_last_partial_solve_wit_1 : mu_json_token_is_last_partial_solve_wit_1.
Axiom proof_of_mu_json_token_is_last_partial_solve_wit_2 : mu_json_token_is_last_partial_solve_wit_2.
Axiom proof_of_mu_json_token_is_last_partial_solve_wit_3_pure : mu_json_token_is_last_partial_solve_wit_3_pure.
Axiom proof_of_mu_json_token_is_last_partial_solve_wit_3 : mu_json_token_is_last_partial_solve_wit_3.
Axiom proof_of_skip_whitespace_safety_wit_1 : skip_whitespace_safety_wit_1.
Axiom proof_of_skip_whitespace_safety_wit_2 : skip_whitespace_safety_wit_2.
Axiom proof_of_skip_whitespace_safety_wit_3 : skip_whitespace_safety_wit_3.
Axiom proof_of_skip_whitespace_safety_wit_4 : skip_whitespace_safety_wit_4.
Axiom proof_of_skip_whitespace_safety_wit_5 : skip_whitespace_safety_wit_5.
Axiom proof_of_skip_whitespace_safety_wit_6 : skip_whitespace_safety_wit_6.
Axiom proof_of_skip_whitespace_entail_wit_1 : skip_whitespace_entail_wit_1.
Axiom proof_of_skip_whitespace_entail_wit_2_1 : skip_whitespace_entail_wit_2_1.
Axiom proof_of_skip_whitespace_entail_wit_2_2 : skip_whitespace_entail_wit_2_2.
Axiom proof_of_skip_whitespace_entail_wit_2_3 : skip_whitespace_entail_wit_2_3.
Axiom proof_of_skip_whitespace_entail_wit_2_4 : skip_whitespace_entail_wit_2_4.
Axiom proof_of_skip_whitespace_return_wit_1 : skip_whitespace_return_wit_1.
Axiom proof_of_skip_whitespace_return_wit_2 : skip_whitespace_return_wit_2.
Axiom proof_of_skip_whitespace_partial_solve_wit_1_pure : skip_whitespace_partial_solve_wit_1_pure.
Axiom proof_of_skip_whitespace_partial_solve_wit_1 : skip_whitespace_partial_solve_wit_1.
Axiom proof_of_skip_whitespace_partial_solve_wit_2_pure : skip_whitespace_partial_solve_wit_2_pure.
Axiom proof_of_skip_whitespace_partial_solve_wit_2 : skip_whitespace_partial_solve_wit_2.
Axiom proof_of_skip_whitespace_partial_solve_wit_3_pure : skip_whitespace_partial_solve_wit_3_pure.
Axiom proof_of_skip_whitespace_partial_solve_wit_3 : skip_whitespace_partial_solve_wit_3.
Axiom proof_of_skip_whitespace_partial_solve_wit_4_pure : skip_whitespace_partial_solve_wit_4_pure.
Axiom proof_of_skip_whitespace_partial_solve_wit_4 : skip_whitespace_partial_solve_wit_4.
Axiom proof_of_skip_whitespace_partial_solve_wit_5_pure : skip_whitespace_partial_solve_wit_5_pure.
Axiom proof_of_skip_whitespace_partial_solve_wit_5 : skip_whitespace_partial_solve_wit_5.
Axiom proof_of_skip_whitespace_partial_solve_wit_6_pure : skip_whitespace_partial_solve_wit_6_pure.
Axiom proof_of_skip_whitespace_partial_solve_wit_6 : skip_whitespace_partial_solve_wit_6.
Axiom proof_of_is_number_prefix_safety_wit_1 : is_number_prefix_safety_wit_1.
Axiom proof_of_is_number_prefix_safety_wit_2 : is_number_prefix_safety_wit_2.
Axiom proof_of_is_number_prefix_safety_wit_3 : is_number_prefix_safety_wit_3.
Axiom proof_of_is_number_prefix_return_wit_1 : is_number_prefix_return_wit_1.
Axiom proof_of_is_number_prefix_return_wit_2 : is_number_prefix_return_wit_2.
Axiom proof_of_is_number_prefix_return_wit_3 : is_number_prefix_return_wit_3.
Axiom proof_of_is_number_prefix_return_wit_4 : is_number_prefix_return_wit_4.
Axiom proof_of_is_hex_safety_wit_1 : is_hex_safety_wit_1.
Axiom proof_of_is_hex_safety_wit_2 : is_hex_safety_wit_2.
Axiom proof_of_is_hex_safety_wit_3 : is_hex_safety_wit_3.
Axiom proof_of_is_hex_safety_wit_4 : is_hex_safety_wit_4.
Axiom proof_of_is_hex_safety_wit_5 : is_hex_safety_wit_5.
Axiom proof_of_is_hex_safety_wit_6 : is_hex_safety_wit_6.
Axiom proof_of_is_hex_safety_wit_7 : is_hex_safety_wit_7.
Axiom proof_of_is_hex_safety_wit_8 : is_hex_safety_wit_8.
Axiom proof_of_is_hex_safety_wit_9 : is_hex_safety_wit_9.
Axiom proof_of_is_hex_safety_wit_10 : is_hex_safety_wit_10.
Axiom proof_of_is_hex_safety_wit_11 : is_hex_safety_wit_11.
Axiom proof_of_is_hex_safety_wit_12 : is_hex_safety_wit_12.
Axiom proof_of_is_hex_return_wit_1 : is_hex_return_wit_1.
Axiom proof_of_is_hex_return_wit_2 : is_hex_return_wit_2.
Axiom proof_of_is_hex_return_wit_3 : is_hex_return_wit_3.
Axiom proof_of_is_hex_return_wit_4 : is_hex_return_wit_4.
Axiom proof_of_is_hex_return_wit_5 : is_hex_return_wit_5.
Axiom proof_of_is_hex_return_wit_6 : is_hex_return_wit_6.
Axiom proof_of_is_hex_return_wit_7 : is_hex_return_wit_7.
Axiom proof_of_set_token_string_return_wit_1 : set_token_string_return_wit_1.
Axiom proof_of_get_token_string_return_wit_1 : get_token_string_return_wit_1.
Axiom proof_of_set_token_string_length_safety_wit_1 : set_token_string_length_safety_wit_1.
Axiom proof_of_set_token_string_length_safety_wit_2 : set_token_string_length_safety_wit_2.
Axiom proof_of_set_token_string_length_return_wit_1 : set_token_string_length_return_wit_1.
Axiom proof_of_set_token_type_safety_wit_1 : set_token_type_safety_wit_1.
Axiom proof_of_set_token_type_safety_wit_2 : set_token_type_safety_wit_2.
Axiom proof_of_set_token_type_return_wit_1 : set_token_type_return_wit_1.
Axiom proof_of_set_token_level_safety_wit_1 : set_token_level_safety_wit_1.
Axiom proof_of_set_token_level_safety_wit_2 : set_token_level_safety_wit_2.
Axiom proof_of_set_token_level_return_wit_1 : set_token_level_return_wit_1.
Axiom proof_of_set_token_is_last_safety_wit_1 : set_token_is_last_safety_wit_1.
Axiom proof_of_set_token_is_last_safety_wit_2 : set_token_is_last_safety_wit_2.
Axiom proof_of_set_token_is_last_return_wit_1 : set_token_is_last_return_wit_1.

End VC_Correct.
