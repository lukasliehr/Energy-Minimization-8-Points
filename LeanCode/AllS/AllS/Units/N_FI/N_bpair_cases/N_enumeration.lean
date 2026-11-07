import AllS.Units.N_FI.N_bpair_cases.N_eta_interval

namespace Blueprint.Thomson.Finite

theorem bpair_cases_enumeration (i j k : ℕ) (eta : ℝ)
    (hij : i+j ≤ 2) (hik : i+k ≤ 2) (hjk : j+k ≤ 2)
    (he0 : 0 < eta) (he1 : eta < 1)
    (heq : (j:ℝ)+(k:ℝ)-2=eta*((i:ℝ)-(j:ℝ))) :
    (i=0 ∧ j=0 ∧ k=2) ∨ (i=1 ∧ j=1 ∧ k=1) := by
  have hi : i ≤ 2 := by omega
  have hj : j ≤ 2 := by omega
  have hk : k ≤ 2 := by omega
  interval_cases i <;> interval_cases j <;> interval_cases k <;> norm_num at * <;> linarith

#check bpair_cases_enumeration
#print axioms bpair_cases_enumeration
end Blueprint.Thomson.Finite
