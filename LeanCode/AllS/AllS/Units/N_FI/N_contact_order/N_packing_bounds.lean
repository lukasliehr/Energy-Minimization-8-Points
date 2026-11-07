import Blueprint.FiniteDefinitions

noncomputable section
open Real
namespace Blueprint.Thomson.Finite

/-- Exact packing endpoint facts from the quadratic equation for sqrt 2. -/
theorem packing_endpoint_bounds : 13/50 < aInf ∧ aInf < 1/3 ∧
    7*aInf^2+2*aInf-1=0 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  have hl : (141/100 : ℝ) < √2 := by nlinarith
  have hu : √(2 : ℝ) < 3/2 := by nlinarith
  dsimp [aInf]
  refine ⟨by linarith, by linarith, ?_⟩
  nlinarith

theorem contact_order_packing_bounds (a : ℝ) (hl : aInf < a) (hu : a < 1/3) :
    (13/50 < aInf ∧ aInf < a ∧ a < 1/3) ∧ 0 < 7*a^2+2*a-1 := by
  obtain ⟨hb, _, he⟩ := packing_endpoint_bounds
  refine ⟨⟨hb, hl, hu⟩, ?_⟩
  have hprod : 0 < (a-aInf)*(7*a+7*aInf+2) :=
    mul_pos (sub_pos.mpr hl) (by linarith)
  nlinarith

#check contact_order_packing_bounds
#print axioms contact_order_packing_bounds
end Blueprint.Thomson.Finite
