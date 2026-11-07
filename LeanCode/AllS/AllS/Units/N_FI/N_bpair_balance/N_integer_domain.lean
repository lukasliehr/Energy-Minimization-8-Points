import AllS.Units.N_FI.N_bpair_balance.N_symmetry

namespace Blueprint.Thomson.Finite

theorem bpair_balance_integer_domain (n : Fin 3 → Fin 3 → ℕ)
    (hsym : ∀ u v, n u v=n v u) (hrow : ∀ u, (∑ v, n u v)=2) :
    n 0 0=2-n 0 1-n 0 2 ∧ n 1 1=2-n 0 1-n 1 2 ∧ n 2 2=2-n 0 2-n 1 2 ∧
    n 0 1+n 0 2 ≤ 2 ∧ n 0 1+n 1 2 ≤ 2 ∧ n 0 2+n 1 2 ≤ 2 := by
  have h0 := hrow 0
  have h1 := hrow 1
  have h2 := hrow 2
  rw [Fin.sum_univ_three] at h0 h1 h2
  rw [hsym 1 0] at h1
  rw [hsym 2 0,hsym 2 1] at h2
  omega

#check bpair_balance_integer_domain
#print axioms bpair_balance_integer_domain
end Blueprint.Thomson.Finite
