import AllS.Units.N_FI.N_bpair_balance.N_integer_domain

namespace Blueprint.Thomson.Finite

theorem bpair_contact_matrix_symmetric {a : ℝ} {Y : Fin 8 → Point} (h : ContactCountData a Y)
    (h3 : oddMoment 3 Y=0) (r t : Fin 8) (hrt : r ≠ t)
    (hB : inner ℝ (Y r) (Y t)=contacts a 1) :
    let n := bpairCounts a Y r t
    (∀ u, (∑ v, n u v)=2) ∧ (∀ v, (∑ u, n u v)=2) ∧ (∀ u v, n u v=n v u) ∧
    n 0 0=2-n 0 1-n 0 2 ∧ n 1 1=2-n 0 1-n 1 2 ∧ n 2 2=2-n 0 2-n 1 2 ∧
    n 0 1+n 0 2 ≤ 2 ∧ n 0 1+n 1 2 ≤ 2 ∧ n 0 2+n 1 2 ≤ 2 := by
  obtain ⟨_,hr,hc⟩ := bpair_balance_contingency h r t hrt hB
  have hs := bpair_balance_symmetry h h3 r t hrt hB
  exact ⟨hr,hc,hs,bpair_balance_integer_domain _ hs hr⟩

#check bpair_contact_matrix_symmetric
#print axioms bpair_contact_matrix_symmetric
end Blueprint.Thomson.Finite
