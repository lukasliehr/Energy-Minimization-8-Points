import Lean_Code.RhombusGram

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma rhombus_cosine_ratio_Ioo (c x : ℝ) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hxlo : 2 * c ^ 2 - 1 < x) (hxhi : x < 1) :
    (x - c ^ 2) / (1 - c ^ 2) ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hden : 0 < 1 - c ^ 2 := by nlinarith [mul_pos hc.1 (sub_pos.mpr hc.2)]
  constructor
  · apply (lt_div_iff₀ hden).mpr
    linarith
  · apply (div_lt_one hden).mpr
    linarith

lemma rhombus_half_angle_square (c x θ : ℝ) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hx : 2 * c ^ 2 - 1 < x) (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi)
    (hcos : Real.cos θ = (x - c ^ 2) / (1 - c ^ 2)) :
    Real.tan (θ / 2) ^ 2 = (1 - x) / (1 + x - 2 * c ^ 2) := by
  have hC : 0 < 1 - c ^ 2 := by nlinarith [mul_pos hc.1 (sub_pos.mpr hc.2)]
  have hd : 0 < 1 + x - 2 * c ^ 2 := by linarith
  rw [tan_half_sq_identity θ hθ, hcos]
  have hplus : 1 + (x - c ^ 2) / (1 - c ^ 2) = (1 + x - 2 * c ^ 2) / (1 - c ^ 2) := by
    field_simp [hC.ne']
    ring
  have hminus : 1 - (x - c ^ 2) / (1 - c ^ 2) = (1 - x) / (1 - c ^ 2) := by
    field_simp [hC.ne']
    ring
  rw [hplus, hminus]
  field_simp [hC.ne', hd.ne']

theorem rhombus_tangent_relation_of_diagonals (c x y : ℝ)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hx : x ∈ Set.Ico (-1 : ℝ) 1) (hy : y ∈ Set.Ico (-1 : ℝ) 1)
    (hrel : (1 + x) * (1 + y) = 4 * c ^ 2) :
    let β := Real.arccos ((y - c ^ 2) / (1 - c ^ 2))
    let δ := Real.arccos ((x - c ^ 2) / (1 - c ^ 2))
    β ∈ Set.Ioo (0 : ℝ) Real.pi ∧ δ ∈ Set.Ioo (0 : ℝ) Real.pi ∧
      Real.tan (β / 2) * Real.tan (δ / 2) = 1 / c := by
  let β := Real.arccos ((y - c ^ 2) / (1 - c ^ 2))
  let δ := Real.arccos ((x - c ^ 2) / (1 - c ^ 2))
  have hshort := rhombus_diagonals_short_scalar c x y hc.1 hx hy hrel
  have hrx := rhombus_cosine_ratio_Ioo c x hc hshort.1 hx.2
  have hry := rhombus_cosine_ratio_Ioo c y hc hshort.2 hy.2
  have hβ : β ∈ Set.Ioo (0 : ℝ) Real.pi :=
    ⟨Real.arccos_pos.mpr hry.2, Real.arccos_lt_pi.mpr hry.1⟩
  have hδ : δ ∈ Set.Ioo (0 : ℝ) Real.pi :=
    ⟨Real.arccos_pos.mpr hrx.2, Real.arccos_lt_pi.mpr hrx.1⟩
  have hβcos : Real.cos β = (y - c ^ 2) / (1 - c ^ 2) := Real.cos_arccos hry.1.le hry.2.le
  have hδcos : Real.cos δ = (x - c ^ 2) / (1 - c ^ 2) := Real.cos_arccos hrx.1.le hrx.2.le
  have hβsq := rhombus_half_angle_square c y β hc hshort.2 hβ hβcos
  have hδsq := rhombus_half_angle_square c x δ hc hshort.1 hδ hδcos
  have hdx : 0 < 1 + x - 2 * c ^ 2 := by linarith [hshort.1]
  have hdy : 0 < 1 + y - 2 * c ^ 2 := by linarith [hshort.2]
  have hpoly : c ^ 2 * (1 - x) * (1 - y) =
      (1 + x - 2 * c ^ 2) * (1 + y - 2 * c ^ 2) := by
    nlinarith [congrArg (fun z : ℝ => c ^ 2 * z) hrel]
  have hsquare : (Real.tan (β / 2) * Real.tan (δ / 2)) ^ 2 = (1 / c) ^ 2 := by
    rw [mul_pow, hβsq, hδsq]
    field_simp [hc.1.ne', hdx.ne', hdy.ne']
    nlinarith [hpoly]
  have hpβ : 0 < Real.tan (β / 2) := Real.tan_pos_of_pos_of_lt_pi_div_two
    (by linarith [hβ.1]) (by linarith [hβ.2])
  have hpδ : 0 < Real.tan (δ / 2) := Real.tan_pos_of_pos_of_lt_pi_div_two
    (by linarith [hδ.1]) (by linarith [hδ.2])
  refine ⟨hβ, hδ, ?_⟩
  nlinarith [mul_pos hpβ hpδ, one_div_pos.mpr hc.1]

/-- The spherical rhombus relation for the actual angles obtained by
projecting the four unit vertices to their tangent planes. -/
theorem contact_rhombus_relation (Y : Fin 4 → ℝ³) (c : ℝ)
    (hY : ∀ i, ‖Y i‖ = 1) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (h02 : Y 0 ≠ Y 2) (h13 : Y 1 ≠ Y 3)
    (h01 : inner ℝ (Y 0) (Y 1) = c) (h12 : inner ℝ (Y 1) (Y 2) = c)
    (h23 : inner ℝ (Y 2) (Y 3) = c) (h30 : inner ℝ (Y 3) (Y 0) = c) :
    contactAngle c (Y 1) (Y 3) ∈ Set.Ioo (0 : ℝ) Real.pi ∧
    contactAngle c (Y 0) (Y 2) ∈ Set.Ioo (0 : ℝ) Real.pi ∧
    Real.tan (contactAngle c (Y 1) (Y 3) / 2) *
      Real.tan (contactAngle c (Y 0) (Y 2) / 2) = 1 / c := by
  have hxlow : -1 ≤ inner ℝ (Y 0) (Y 2) := by
    have h := abs_real_inner_le_norm (Y 0) (Y 2)
    rw [hY 0, hY 2, one_mul] at h
    exact (abs_le.mp h).1
  have hylow : -1 ≤ inner ℝ (Y 1) (Y 3) := by
    have h := abs_real_inner_le_norm (Y 1) (Y 3)
    rw [hY 1, hY 3, one_mul] at h
    exact (abs_le.mp h).1
  exact rhombus_tangent_relation_of_diagonals c _ _ hc
    ⟨hxlow, unit_inner_lt_one _ _ (hY 0) (hY 2) h02⟩
    ⟨hylow, unit_inner_lt_one _ _ (hY 1) (hY 3) h13⟩
    (rhombus_diagonal_identity Y c hY h02 h13 h01 h12 h23 h30)

end SquareAntiprismVerification
