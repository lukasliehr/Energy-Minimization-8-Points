import AllS.Units.N_GI.N_weighted_two_value.N_two_value_formula

noncomputable section
open Real
open scoped BigOperators
namespace Blueprint.Thomson.Tail.Implementation

theorem weighted_two_value_assemble {n : ℕ} (hn : 2 ≤ n) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (v : ℝ) (hv : 0 < v) :
    ∃ x ∈ weightedFeasible w v, IsMinOn (weightedExp w) (weightedFeasible w v) x ∧
    ∃ z : ℝ, 0 < z ∧ z < ∑ i,w i ∧ z=weightedNegativeMass w x ∧
      (∀ i, x i=-v*√(((∑ j,w j)-z)/((∑ j,w j)*z)) ∨
        x i=v*√(z/((∑ j,w j)*((∑ j,w j)-z)))) ∧
      (∃ i, x i=-v*√(((∑ j,w j)-z)/((∑ j,w j)*z))) ∧
      (∃ i, x i=v*√(z/((∑ j,w j)*((∑ j,w j)-z)))) ∧
      weightedExp w x=twoValueExp (∑ i,w i) v z := by
  obtain ⟨x,hx,hmin,a,b,haff⟩ := weighted_two_value_minimum_and_tangents hn w hw v hv
  exact ⟨x,hx,hmin,weighted_two_value_two_value_formula hn w hw v hv x hx a b haff⟩

#check weighted_two_value_assemble
#print axioms weighted_two_value_assemble
end Blueprint.Thomson.Tail.Implementation
