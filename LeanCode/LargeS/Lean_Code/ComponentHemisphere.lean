import Lean_Code.ContactComponents

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- An irreducible, nonisolated contact component cannot lie in a closed
hemisphere. At a vertex minimizing the pole coordinate, the direction
away from the pole is a forbidden pushing direction. -/
theorem irreducible_closed_set_not_hemisphere (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : ∀ i, ‖Y i‖ = 1) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hirr : PackingIrreducible c Y) (V : Finset (Fin 8)) (hV : V.Nonempty)
    (hnonisolated : ∀ i ∈ V, ∃ j, j ≠ i ∧ inner ℝ (Y i) (Y j) = c)
    (hclosed : ∀ i ∈ V, ∀ j, j ≠ i → inner ℝ (Y i) (Y j) = c → j ∈ V)
    (p : ℝ³) (hp : ‖p‖ = 1) : ∃ i ∈ V, inner ℝ p (Y i) < 0 := by
  classical
  by_contra h
  push_neg at h
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image V (fun i => inner ℝ p (Y i)) hV
  let a := inner ℝ p (Y i)
  let v := a • Y i - p
  have ha : 0 ≤ a := h i hi
  have hpi : inner ℝ (Y i) p = a := real_inner_comm p (Y i)
  have hvorth : inner ℝ (Y i) v = 0 := by
    simp [v, inner_sub_right, inner_smul_right, hY i, hpi]
  have hvinner (j : Fin 8) (hji : j ≠ i) (hij : inner ℝ (Y i) (Y j) = c) :
      inner ℝ v (Y j) ≤ 0 := by
    have hminj := hmin j (hclosed i hi j hji hij)
    have hac : a * c ≤ a := mul_le_of_le_one_right ha hc.2.le
    simp only [v, inner_sub_left, inner_smul_left, starRingEnd_apply, star_trivial, hij]
    change a ≤ inner ℝ p (Y j) at hminj
    linarith
  have hvne : v ≠ 0 := by
    intro hvzero
    have hpeq : p = a • Y i := (sub_eq_zero.mp hvzero).symm
    by_cases hazero : a = 0
    · rw [hazero, zero_smul] at hpeq
      rw [hpeq, norm_zero] at hp
      norm_num at hp
    · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm hazero)
      obtain ⟨j, hji, hij⟩ := hnonisolated i hi
      have hminj := hmin j (hclosed i hi j hji hij)
      change a ≤ inner ℝ p (Y j) at hminj
      rw [hpeq] at hminj
      simp only [inner_smul_left, starRingEnd_apply, star_trivial, hij] at hminj
      nlinarith [mul_pos hapos (sub_pos.mpr hc.2)]
  apply hirr i (hnonisolated i hi)
  refine ⟨‖v‖⁻¹ • v, ?_, ?_, ?_⟩
  · simp [norm_smul, hvne]
  · simp [inner_smul_right, hvorth]
  · intro j hji hij
    simp only [inner_smul_left, starRingEnd_apply, star_trivial]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg v)) (hvinner j hji hij)

theorem irreducible_component_not_hemisphere (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : ∀ i, ‖Y i‖ = 1) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hirr : PackingIrreducible c Y) (root : Fin 8)
    (hroot : ∃ j, j ≠ root ∧ inner ℝ (Y root) (Y j) = c)
    (p : ℝ³) (hp : ‖p‖ = 1) :
    ∃ i ∈ contactComponent Y c root, inner ℝ p (Y i) < 0 := by
  apply irreducible_closed_set_not_hemisphere Y c hY hc hirr (contactComponent Y c root)
    ⟨root, contactComponent_root Y c root⟩ ?_ ?_ p hp
  · intro i hi
    have hroot' : ∃ j, ContactAdj Y c root j := by
      obtain ⟨j, hji, hij⟩ := hroot
      exact ⟨j, hji.symm, hij⟩
    obtain ⟨j, hij⟩ := reachable_nonisolated ((mem_contactComponent Y c root i).mp hi) hroot'
    exact ⟨j, hij.1.symm, hij.2⟩
  · intro i hi j hji hij
    exact contactComponent_closed Y c root i j hi ⟨hji.symm, hij⟩

end SquareAntiprismVerification
