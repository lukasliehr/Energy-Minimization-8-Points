import Blueprint.Target
import Lean_Code.Parameter

noncomputable section
open Real

namespace Blueprint
open Thomson

theorem root_spec : RootSpec := by
  refine ⟨SquareAntiprismVerification.aStar, ?_, SquareAntiprismVerification.aStar_zero⟩
  intro s hs
  refine ⟨(SquareAntiprismVerification.aStar_spec s hs).1, ?_⟩
  intro b hb
  constructor
  · exact SquareAntiprismVerification.aStar_unique s hs b hb
  · intro h
    rw [h]
    exact (SquareAntiprismVerification.aStar_spec s hs).2

theorem stationary_root_unique (s : ℝ) (hs : 0 ≤ s) :
    ∃! a : ℝ, a ∈ Set.Ioo (0 : ℝ) 1 ∧ F s a = 0 :=
  SquareAntiprismVerification.F_root_exists_unique s hs

theorem antiprism_coordinates (a : ℝ) : SquareAntiprismVerification.X a = X a := by
  have htwo : (2 : ℝ) * π / 2 = π := by ring
  have hthree : (3 : ℝ) * π / 2 = π + π / 2 := by ring
  have hsqrt : (√(2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt_ne : √(2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hdiv : ∀ r : ℝ, r * (√2 / 2) = r / √2 := by
    intro r
    field_simp
    linear_combination r * hsqrt
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X, SquareAntiprismVerification.X, SquareAntiprismVerification.r,
      SquareAntiprismVerification.h, Fin.append, Fin.addCases, htwo, hthree,
      Real.cos_add, Real.sin_add, hdiv, mul_neg]

theorem antiprism_is_configuration (a : ℝ) (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    IsConfiguration (X a) := by
  rw [← antiprism_coordinates]
  exact SquareAntiprismVerification.X_isConfiguration a ha

theorem positive_energy_bridge (s : ℝ) (hs : 0 < s) (Y : Fin 8 → Point) :
    E s Y = SquareAntiprismVerification.E s Y := by
  simp only [E, SquareAntiprismVerification.E, if_neg (ne_of_gt hs)]

theorem configuration_bridge (Y : Fin 8 → Point) :
    IsConfiguration Y ↔ SquareAntiprismVerification.IsConfiguration Y := Iff.rfl

-- The upstream relation is written in the reverse direction.
theorem congruence_bridge (Y Z : Fin 8 → Point) :
    Thomson.Congruent Y Z ↔ SquareAntiprismVerification.Congruent Z Y := Iff.rfl

#print axioms root_spec
#print axioms antiprism_coordinates
end Blueprint
