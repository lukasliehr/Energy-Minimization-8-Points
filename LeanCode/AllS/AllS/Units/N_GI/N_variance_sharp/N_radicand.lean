import AllS.Units.N_GI.N_variance_basic.N_lower_helpers

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem variance_sharp_radicand (r : ℝ) (hr0 : 0≤r) (hr3 : r≤3/10) :
    (49:ℝ)/16≤17/5-(15/4)*r^2 ∧ 0<(17:ℝ)/5-(15/4)*r^2 := by
  constructor <;> nlinarith

#print axioms variance_sharp_radicand
end Blueprint.Thomson.Tail.Implementation
