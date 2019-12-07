theory Checker_Codegen
  imports Main Sorting_Network Checker "HOL-Library.Code_Target_Numeral"
begin

lemma check_proof_get_bound_spec:
  assumes \<open>check_proof_get_bound cert = Some (width, bound)\<close>
  shows \<open>lower_size_bound_for_width (nat width) (nat bound)\<close>
  using assms by (rule Checker.check_proof_get_bound_spec)

definition nat_pred_code :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>nat_pred_code n = (case n of 0 \<Rightarrow> nat.pred 0 | Suc n' \<Rightarrow> n')\<close>

lemma nat_pred_code[code]: \<open>nat.pred = nat_pred_code\<close>
  by (rule; metis nat_pred_code_def old.nat.simps(4) pred_def)

export_code
    check_proof_get_bound integer_of_int int_of_integer
    ProofCert ProofStep HuffmanWitnesses SuccessorWitnesses ProofWitness
  in Haskell module_name Verified.Checker file_prefix "checker"

end