import Lean_Code.RotationSystem

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma cyclic_sign_transition {n : ℕ} (f : Fin (n + 1) → ℝ)
    (hpos : ∃ i, 0 < f i) (hneg : ∃ j, f j < 0) :
    ∃ k, 0 ≤ f k ∧ f (k + 1) ≤ 0 := by
  classical
  obtain ⟨i, hi⟩ := hpos
  obtain ⟨j, hj⟩ := hneg
  let g : Fin (n + 1) → ℝ := fun k => f (j + k)
  let V : Finset (Fin (n + 1)) := Finset.univ.filter (fun k => 0 < g k)
  have hV : V.Nonempty := by
    refine ⟨i - j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simpa [g, add_sub_cancel_left] using hi
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image V (fun k => k.val) hV
  have hkpos : 0 < g k := (Finset.mem_filter.mp hk).2
  have hnext : g (k + 1) ≤ 0 := by
    by_cases hlast : k = Fin.last n
    · subst k
      simpa [g] using hj.le
    · by_contra hn
      have hmem : k + 1 ∈ V := Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge hn⟩
      have hm := hmax (k + 1) hmem
      rw [Fin.val_add_one, if_neg hlast] at hm
      omega
  exact ⟨j + k, hkpos.le, by simpa only [g, add_assoc] using hnext⟩

lemma irreducible_tangent_positive (Y : Fin 8 → ℝ³) (c : ℝ)
    (hirr : PackingIrreducible c Y) (i : Fin 8)
    (hne : ∃ j, j ≠ i ∧ inner ℝ (Y i) (Y j) = c)
    (v : ℝ³) (hv : v ≠ 0) (horth : inner ℝ (Y i) v = 0) :
    ∃ j, j ≠ i ∧ inner ℝ (Y i) (Y j) = c ∧ 0 < inner ℝ v (Y j) := by
  by_contra hn
  apply hirr i hne
  refine ⟨‖v‖⁻¹ • v, ?_, ?_, ?_⟩
  · simp [norm_smul, hv]
  · simp [inner_smul_right, horth]
  · intro j hji hij
    have hle : inner ℝ v (Y j) ≤ 0 := by
      by_contra h
      exact hn ⟨j, hji, hij, lt_of_not_ge h⟩
    simp only [inner_smul_left, starRingEnd_apply, star_trivial]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg v)) hle

lemma triple_swap_last (p q z : ℝ³) :
    inner ℝ (crossVec p q) z = -inner ℝ (crossVec p z) q := by
  rw [triple_cyclic, triple_cyclic, crossVec_swap, inner_neg_left]

namespace ContactOrderData

variable {Y : Fin 8 → ℝ³} {c : ℝ} {i : Fin 8}

/-- The actual consecutive contact sectors cover every direction about a
nonisolated irreducible vertex. Zero tangent projection is included. -/
theorem sectors_cover (D : ContactOrderData Y c i) (hirr : PackingIrreducible c Y) (z : ℝ³) :
    ∃ k, 0 ≤ inner ℝ (crossVec (Y i) (Y (D.label k))) z ∧
      0 ≤ inner ℝ (crossVec (Y (D.label (k + 1))) (Y i)) z := by
  let v := crossVec (Y i) z
  have horth : inner ℝ (Y i) v = 0 := by rw [real_inner_comm]; exact crossVec_inner_left _ _
  have hphase (k : Fin (D.size + 1)) :
      inner ℝ (crossVec (Y i) (Y (D.label k))) z = -inner ℝ v (Y (D.label k)) :=
    triple_swap_last _ _ _
  by_cases hv : v = 0
  · refine ⟨0, ?_, ?_⟩
    · rw [hphase, hv, inner_zero_left]; norm_num
    · rw [crossVec_swap, inner_neg_left, hphase, hv, inner_zero_left]; norm_num
  · have hne : ∃ j, j ≠ i ∧ inner ℝ (Y i) (Y j) = c := ⟨D.label 0, D.contact 0⟩
    obtain ⟨a, hai, hac, ha⟩ := irreducible_tangent_positive Y c hirr i hne v hv horth
    obtain ⟨b, hbi, hbc, hb⟩ := irreducible_tangent_positive Y c hirr i hne (-v)
      (neg_ne_zero.mpr hv) (by simp [horth])
    obtain ⟨ka, rfl⟩ := D.covers a hai hac
    obtain ⟨kb, rfl⟩ := D.covers b hbi hbc
    simp only [inner_neg_left] at hb
    obtain ⟨k, hk, hnext⟩ := cyclic_sign_transition
      (fun k => inner ℝ (crossVec (Y i) (Y (D.label k))) z)
      ⟨kb, by rw [hphase]; exact hb⟩ ⟨ka, by rw [hphase]; linarith⟩
    refine ⟨k, hk, ?_⟩
    rw [crossVec_swap, inner_neg_left]
    linarith

end ContactOrderData

theorem contactRotateAt_sectors_cover (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hirr : PackingIrreducible c Y) (i : Fin 8)
    (hne : ∃ j, j ≠ i ∧ inner ℝ (Y i) (Y j) = c) (z : ℝ³) :
    ∃ j : ContactNeighbor Y c i,
      0 ≤ inner ℝ (crossVec (Y i) (Y j)) z ∧
      0 ≤ inner ℝ (crossVec (Y (contactRotateAt Y c hY hc i j)) (Y i)) z := by
  classical
  unfold contactRotateAt
  rw [dif_pos hne]
  let D := Classical.choice (contact_order_exists Y c i hY hc hne)
  obtain ⟨k, hleft, hright⟩ := D.sectors_cover hirr z
  refine ⟨D.labelEquiv k, ?_, ?_⟩
  · exact hleft
  · change 0 ≤ inner ℝ (crossVec (Y (D.successor (D.labelEquiv k))) (Y i)) z
    simpa only [D.successor_label, D.labelEquiv_val] using hright

end SquareAntiprismVerification
