import AllS.Units.N_GI.N_weighted_two_value.N_assemble

noncomputable section
open Real
open scoped BigOperators
namespace Blueprint.Thomson.Tail
open Implementation

theorem weighted_two_value {n : ℕ} (hn : 2 ≤ n) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (v : ℝ) (hv : 0 < v) :
    ∃ x ∈ weightedFeasible w v, IsMinOn (weightedExp w) (weightedFeasible w v) x ∧
    ∃ z : ℝ, 0 < z ∧ z < ∑ i,w i ∧ z=weightedNegativeMass w x ∧
      (∀ i, x i=-v*√(((∑ j,w j)-z)/((∑ j,w j)*z)) ∨
        x i=v*√(z/((∑ j,w j)*((∑ j,w j)-z)))) ∧
      (∃ i, x i=-v*√(((∑ j,w j)-z)/((∑ j,w j)*z))) ∧
      (∃ i, x i=v*√(z/((∑ j,w j)*((∑ j,w j)-z)))) ∧
      weightedExp w x=twoValueExp (∑ i,w i) v z :=
  weighted_two_value_assemble hn w hw v hv

#check weighted_two_value
#print axioms weighted_two_value
end Blueprint.Thomson.Tail
