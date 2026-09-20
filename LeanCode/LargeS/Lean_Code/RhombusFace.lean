import Lean_Code.RhombusBounds

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

def quadrilateralAngle (c : ℝ) (Y : Fin 4 → ℝ³) (j : Fin 4) : ℝ :=
  contactAngle c (Y (j + 3)) (Y (j + 1))

/-- Algebraic spherical excess; its use as total area is derived from
corner-angle sums and Euler's identity in the incidence argument. -/
def quadrilateralExcess (c : ℝ) (Y : Fin 4 → ℝ³) : ℝ :=
  2 * contactAngle c (Y 1) (Y 3) + 2 * contactAngle c (Y 0) (Y 2) - 2 * Real.pi

lemma contactAngle_comm (c : ℝ) (x y : ℝ³) : contactAngle c x y = contactAngle c y x := by
  unfold contactAngle
  rw [real_inner_comm x y]

lemma quadrilateralAngle_alternates (c : ℝ) (Y : Fin 4 → ℝ³) (j : Fin 4) :
    quadrilateralAngle c Y j = if j = 0 ∨ j = 2 then contactAngle c (Y 1) (Y 3)
      else contactAngle c (Y 0) (Y 2) := by
  fin_cases j
  · exact contactAngle_comm c (Y 3) (Y 1)
  · rfl
  · rfl
  · exact contactAngle_comm c (Y 2) (Y 0)

lemma quadrilateralAngle_sum (c : ℝ) (Y : Fin 4 → ℝ³) :
    ∑ j, quadrilateralAngle c Y j = quadrilateralExcess c Y + 2 * Real.pi := by
  simp only [quadrilateralAngle_alternates, Fin.sum_univ_succ]
  norm_num [Fin.ext_iff, quadrilateralExcess]
  ring

theorem quadrilateral_geometry (Y : Fin 4 → ℝ³) (c : ℝ)
    (hY : ∀ i, ‖Y i‖ = 1) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hinj : Function.Injective Y)
    (hside : ∀ j : Fin 4, inner ℝ (Y j) (Y (j + 1)) = c)
    (h02 : inner ℝ (Y 0) (Y 2) < c) (h13 : inner ℝ (Y 1) (Y 3) < c) :
    ∀ j : Fin 4,
      quadrilateralAngle c Y j ∈ Set.Ioo (Real.arccos (c / (1 + c))) (2 * Real.arccos (c / (1 + c))) ∧
      quadrilateralExcess c Y = rhombusArea (1 / c) (quadrilateralAngle c Y j) := by
  have hne02 : Y 0 ≠ Y 2 := fun h => (by decide : (0 : Fin 4) ≠ 2) (hinj h)
  have hne13 : Y 1 ≠ Y 3 := fun h => (by decide : (1 : Fin 4) ≠ 3) (hinj h)
  have h01 : inner ℝ (Y 0) (Y 1) = c := hside 0
  have h12 : inner ℝ (Y 1) (Y 2) = c := hside 1
  have h23 : inner ℝ (Y 2) (Y 3) = c := hside 2
  have h30 : inner ℝ (Y 3) (Y 0) = c := hside 3
  obtain ⟨hβbound, hδbound⟩ := contact_rhombus_angle_strict_bounds Y c hY hc hne02 hne13
    h01 h12 h23 h30 h02 h13
  obtain ⟨hβ, hδ, hrel⟩ := contact_rhombus_relation Y c hY hc hne02 hne13 h01 h12 h23 h30
  have hd := rhombusDelta_unique (1 / c) _ _ (one_div_pos.mpr hc.1) hβ hδ hrel
  have hb := rhombusDelta_unique (1 / c) _ _ (one_div_pos.mpr hc.1) hδ hβ (by simpa [mul_comm] using hrel)
  intro j
  rw [quadrilateralAngle_alternates]
  split_ifs
  · refine ⟨hβbound, ?_⟩
    unfold quadrilateralExcess rhombusArea
    rw [← hd]
  · refine ⟨hδbound, ?_⟩
    unfold quadrilateralExcess rhombusArea
    rw [← hb]
    ring

end SquareAntiprismVerification
