import AllS.Units.N_FI.N_contact_order.N_packing_bounds

noncomputable section
open Real
namespace Blueprint.Thomson.Finite

theorem contact_order_ordered_contacts (a : ℝ) (ha : physical a) :
    -1 < contacts a 3 ∧ contacts a 3 < contacts a 1 ∧ contacts a 1 < 0 ∧
    0 < contacts a 2 ∧ contacts a 2 < contacts a 0 ∧ contacts a 0 < 1 ∧
    contacts a 0 + contacts a 1 = 3*a-1 ∧ contacts a 0 + contacts a 1 < 0 := by
  obtain ⟨hl, hu⟩ := ha
  have hb := packing_endpoint_bounds.1
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  have hrlo : (1 : ℝ) < √2 := by nlinarith
  have hrhi : √(2 : ℝ) < 2 := by nlinarith
  have hrne : √(2 : ℝ) ≠ 0 := by positivity
  have hinv : (√(2 : ℝ))⁻¹ = √2/2 := by
    field_simp [hrne]
    nlinarith
  have hD := mul_pos (show 0 < 1-a by linarith) (show 0 < 2-√(2 : ℝ) by linarith)
  have hBD := mul_pos (show 0 < a-(1/4 : ℝ) by linarith) (show 0 < 6-√(2 : ℝ) by linarith)
  have hC := mul_pos (show 0 < (1/3 : ℝ)-a by linarith) (show 0 < 2+√(2 : ℝ) by positivity)
  have hAC := mul_pos (sub_pos.mpr hl) (show 0 < 4+√(2 : ℝ) by positivity)
  dsimp [aInf] at hAC
  change -1 < -a-(1-a)/√2 ∧ -a-(1-a)/√2 < 2*a-1 ∧ 2*a-1 < 0 ∧
    0 < -a+(1-a)/√2 ∧ -a+(1-a)/√2 < a ∧ a < 1 ∧
    a+(2*a-1)=3*a-1 ∧ a+(2*a-1)<0
  simp only [div_eq_mul_inv, hinv]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

#check contact_order_ordered_contacts
#print axioms contact_order_ordered_contacts
end Blueprint.Thomson.Finite
