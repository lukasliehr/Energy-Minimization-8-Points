import AllS.Units.N_FI.N_no_antipodes.N_antipodal_identity

noncomputable section
namespace Blueprint.Thomson.Finite

theorem no_antipodes_third_vertex (Y : Fin 8 → Point) (hY : IsConfiguration Y)
    (i j : Fin 8) (hij : i ≠ j) :
    ∃ k, k ≠ i ∧ k ≠ j ∧ (Y j = -Y i →
      inner ℝ (Y i) (Y k) ≠ 1 ∧ inner ℝ (Y i) (Y k) ≠ -1 ∧
      inner ℝ (Y j) (Y k) ≠ 1 ∧ inner ℝ (Y j) (Y k) ≠ -1) := by
  have hex : ∀ i j : Fin 8, ∃ k : Fin 8, k ≠ i ∧ k ≠ j := by decide
  obtain ⟨k,hki,hkj⟩ := hex i j
  refine ⟨k,hki,hkj,?_⟩
  intro hant
  refine ⟨?_,?_,?_,?_⟩
  · intro h
    exact hki (hY.2 (unit_inner_one_eq (Y i) (Y k) (hY.1 i) (hY.1 k) h).symm)
  · intro h
    have hk := no_antipodes_antipodal_identity (Y i) (Y k) (hY.1 i) (hY.1 k) h
    exact hkj (hY.2 (hk.trans hant.symm))
  · intro h
    exact hkj (hY.2 (unit_inner_one_eq (Y j) (Y k) (hY.1 j) (hY.1 k) h).symm)
  · intro h
    have hk := no_antipodes_antipodal_identity (Y j) (Y k) (hY.1 j) (hY.1 k) h
    rw [hant,neg_neg] at hk
    exact hki (hY.2 hk)

#check no_antipodes_third_vertex
#print axioms no_antipodes_third_vertex
end Blueprint.Thomson.Finite
