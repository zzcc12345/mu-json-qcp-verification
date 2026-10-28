From SimpleC.EE.QCP_demos_LLM.mu_json Require Import mu_json_goal mu_json_proof_auto mu_json_proof_manual.

Module VC_Correctness : VC_Correct.
  Include mu_json_proof_auto.
  Include mu_json_proof_manual.
End VC_Correctness.
