import Lean_Code.RhombusRelation

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma equilateral_angle_Ioo (c : ℝ) (hc : c ∈ Set.Ioo (0 : ℝ) 1) :
    Real.arccos (c / (1 + c)) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  have hd : 0 < 1 + c := by linarith [hc.1]
  exact ⟨Real.arccos_pos.mpr ((div_lt_one hd).mpr (by linarith)),
    Real.arccos_lt_pi_div_two.mpr (div_pos hc.1 hd)⟩

lemma equilateral_tan_product (c α : ℝ) (hc : 0 < c)
    (hα : α ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (hcos : Real.cos α = c / (1 + c)) :
    Real.tan α * Real.tan (α / 2) = 1 / c := by
  have hs : 0 < Real.sin (α / 2) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [hα.1]) (by linarith [hα.2, Real.pi_pos])
  have hch : 0 < Real.cos (α / 2) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hα.1, Real.pi_pos], by linarith [hα.2, Real.pi_pos]⟩
  rw [← (equilateral_half_angle_relations c α hc hα hcos).1, Real.tan_eq_sin_div_cos (α / 2)]
  field_simp [hs.ne', hch.ne']

lemma rhombus_angle_upper_of_lower (b α β δ : ℝ)
    (hα : α ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hβ : β ∈ Set.Ioo (0 : ℝ) Real.pi) (hδ : δ ∈ Set.Ioo (0 : ℝ) Real.pi)
    (hδlow : α ≤ δ) (hbase : Real.tan α * Real.tan (α / 2) = b)
    (hrel : Real.tan (β / 2) * Real.tan (δ / 2) = b) : β ≤ 2 * α := by
  have hαhalf : α / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [hα.1, Real.pi_pos], by linarith [hα.2, Real.pi_pos]⟩
  have hδhalf : δ / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [hδ.1, Real.pi_pos], by linarith [hδ.2]⟩
  have hmon : Real.tan (α / 2) ≤ Real.tan (δ / 2) :=
    Real.strictMonoOn_tan.monotoneOn hαhalf hδhalf (by linarith)
  have hposα : 0 < Real.tan (α / 2) := Real.tan_pos_of_pos_of_lt_pi_div_two
    (by linarith [hα.1]) hαhalf.2
  have hposβ : 0 < Real.tan (β / 2) := Real.tan_pos_of_pos_of_lt_pi_div_two
    (by linarith [hβ.1]) (by linarith [hβ.2])
  by_contra h
  have hstrict : Real.tan α < Real.tan (β / 2) := Real.strictMonoOn_tan
    ⟨by linarith [hα.1, Real.pi_pos], hα.2⟩
    ⟨by linarith [hβ.1, Real.pi_pos], by linarith [hβ.2]⟩ (by linarith)
  have h₁ := mul_lt_mul_of_pos_right hstrict hposα
  have h₂ := mul_le_mul_of_nonneg_left hmon hposβ.le
  rw [hbase] at h₁
  rw [hrel] at h₂
  linarith

theorem contact_rhombus_angle_bounds (Y : Fin 4 → ℝ³) (c : ℝ)
    (hY : ∀ i, ‖Y i‖ = 1) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (h02 : Y 0 ≠ Y 2) (h13 : Y 1 ≠ Y 3)
    (h01 : inner ℝ (Y 0) (Y 1) = c) (h12 : inner ℝ (Y 1) (Y 2) = c)
    (h23 : inner ℝ (Y 2) (Y 3) = c) (h30 : inner ℝ (Y 3) (Y 0) = c)
    (hdiag02 : inner ℝ (Y 0) (Y 2) ≤ c) (hdiag13 : inner ℝ (Y 1) (Y 3) ≤ c) :
    let α := Real.arccos (c / (1 + c))
    contactAngle c (Y 1) (Y 3) ∈ Set.Icc α (2 * α) ∧
      contactAngle c (Y 0) (Y 2) ∈ Set.Icc α (2 * α) := by
  let α := Real.arccos (c / (1 + c))
  have hα := equilateral_angle_Ioo c hc
  have hmaxpos : 0 < c / (1 + c) := div_pos hc.1 (by linarith [hc.1])
  have hmaxlt : c / (1 + c) < 1 := (div_lt_one (by linarith [hc.1])).mpr (by linarith)
  have hcos : Real.cos α = c / (1 + c) := Real.cos_arccos (by linarith) hmaxlt.le
  have hbase := equilateral_tan_product c α hc.1 hα hcos
  have h03 : inner ℝ (Y 0) (Y 3) = c := (real_inner_comm (Y 3) (Y 0)).trans h30
  have h10 : inner ℝ (Y 1) (Y 0) = c := (real_inner_comm (Y 0) (Y 1)).trans h01
  have hβlow := contact_angle_lower_bound (Y 0) (Y 1) (Y 3) c (hY 0) (hY 1) (hY 3) hc h01 h03 hdiag13
  have hδlow := contact_angle_lower_bound (Y 1) (Y 0) (Y 2) c (hY 1) (hY 0) (hY 2) hc h10 h12 hdiag02
  obtain ⟨hβ, hδ, hrel⟩ := contact_rhombus_relation Y c hY hc h02 h13 h01 h12 h23 h30
  exact ⟨⟨hβlow, rhombus_angle_upper_of_lower (1 / c) α _ _ hα hβ hδ hδlow hbase hrel⟩,
    ⟨hδlow, rhombus_angle_upper_of_lower (1 / c) α _ _ hα hδ hβ hβlow hbase (by simpa [mul_comm] using hrel)⟩⟩

theorem rhombusArea_strictConcave_equilateral_interval (c α : ℝ)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hα : α ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    StrictConcaveOn ℝ (Set.Icc α (2 * α)) (rhombusArea (1 / c)) := by
  have hb : 1 < 1 / c := (lt_div_iff₀ hc.1).mpr (by linarith [hc.2])
  have h := rhombusArea_strictConcave (1 / c) hb
  have hsub : Set.Icc α (2 * α) ⊆ Set.Ioo (0 : ℝ) Real.pi := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2, hα.1, hα.2]
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  exact h.2 (hsub hx) (hsub hy) hxy ha hb hab

lemma rhombus_angle_strict_upper_of_strict_lower (b α β δ : ℝ)
    (hα : α ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hβ : β ∈ Set.Ioo (0 : ℝ) Real.pi) (hδ : δ ∈ Set.Ioo (0 : ℝ) Real.pi)
    (hδlow : α < δ) (hbase : Real.tan α * Real.tan (α / 2) = b)
    (hrel : Real.tan (β / 2) * Real.tan (δ / 2) = b) : β < 2 * α := by
  refine lt_of_le_of_ne (rhombus_angle_upper_of_lower b α β δ hα hβ hδ hδlow.le hbase hrel) ?_
  intro heq
  have hstrict : Real.tan (α / 2) < Real.tan (δ / 2) := Real.strictMonoOn_tan
    ⟨by linarith [hα.1, Real.pi_pos], by linarith [hα.1, hα.2]⟩
    ⟨by linarith [hδ.1, Real.pi_pos], by linarith [hδ.2]⟩ (by linarith)
  have hpos : 0 < Real.tan α := Real.tan_pos_of_pos_of_lt_pi_div_two hα.1 hα.2
  rw [heq, show 2 * α / 2 = α by ring] at hrel
  have := mul_lt_mul_of_pos_left hstrict hpos
  linarith

theorem contact_rhombus_angle_strict_bounds (Y : Fin 4 → ℝ³) (c : ℝ)
    (hY : ∀ i, ‖Y i‖ = 1) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (h02 : Y 0 ≠ Y 2) (h13 : Y 1 ≠ Y 3)
    (h01 : inner ℝ (Y 0) (Y 1) = c) (h12 : inner ℝ (Y 1) (Y 2) = c)
    (h23 : inner ℝ (Y 2) (Y 3) = c) (h30 : inner ℝ (Y 3) (Y 0) = c)
    (hdiag02 : inner ℝ (Y 0) (Y 2) < c) (hdiag13 : inner ℝ (Y 1) (Y 3) < c) :
    let α := Real.arccos (c / (1 + c))
    contactAngle c (Y 1) (Y 3) ∈ Set.Ioo α (2 * α) ∧
      contactAngle c (Y 0) (Y 2) ∈ Set.Ioo α (2 * α) := by
  let α := Real.arccos (c / (1 + c))
  have hα := equilateral_angle_Ioo c hc
  have hpos : 0 < c / (1 + c) := div_pos hc.1 (by linarith [hc.1])
  have hlt : c / (1 + c) < 1 := (div_lt_one (by linarith [hc.1])).mpr (by linarith)
  have hcos : Real.cos α = c / (1 + c) := Real.cos_arccos (by linarith) hlt.le
  have hbase := equilateral_tan_product c α hc.1 hα hcos
  have h03 : inner ℝ (Y 0) (Y 3) = c := (real_inner_comm (Y 3) (Y 0)).trans h30
  have h10 : inner ℝ (Y 1) (Y 0) = c := (real_inner_comm (Y 0) (Y 1)).trans h01
  have hβlow := contact_angle_strict_lower_bound (Y 0) (Y 1) (Y 3) c (hY 0) (hY 1) (hY 3) hc h01 h03 hdiag13
  have hδlow := contact_angle_strict_lower_bound (Y 1) (Y 0) (Y 2) c (hY 1) (hY 0) (hY 2) hc h10 h12 hdiag02
  obtain ⟨hβ, hδ, hrel⟩ := contact_rhombus_relation Y c hY hc h02 h13 h01 h12 h23 h30
  exact ⟨⟨hβlow, rhombus_angle_strict_upper_of_strict_lower (1 / c) α _ _ hα hβ hδ hδlow hbase hrel⟩,
    ⟨hδlow, rhombus_angle_strict_upper_of_strict_lower (1 / c) α _ _ hα hδ hβ hβlow hbase (by simpa [mul_comm] using hrel)⟩⟩

end SquareAntiprismVerification
