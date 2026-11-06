import AllS.Units.N_GI.N_derivative_stability.N_assemble

noncomputable section
namespace Blueprint.Thomson.Tail
open Implementation

theorem derivative_stability :
    (∀ q : TangentCoordinates, ‖q‖≤3/10 → ‖contactDerivativeMap q-referenceContactMap‖≤12*‖q‖) ∧
    (∀ (p : ℝ), (97:ℝ)/2≤p → ∀ q ξ : TangentCoordinates, q∈convexTailDomain p →
      ξ∈rotationSlice → ξ≠0 → (47:ℝ)/20*‖ξ‖^2<
        ∑ e : ContactIndex, (pairDerivative q e.1 (contactNext e) ξ)^2) :=
  derivative_stability_assemble

#print axioms derivative_stability
end Blueprint.Thomson.Tail
