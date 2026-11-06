import AllS.Units.N_GI.N_full_hessian.N_strict_margin

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem full_hessian_assemble (p : ℝ) (hp : (97:ℝ)/2≤p) (q ξ : TangentCoordinates)
    (hq : q∈convexTailDomain p) (hξ : ξ∈rotationSlice) (hξ0 : ξ≠0) :
    HasDerivAt (deriv (fun t : ℝ=>squaredEnergy p (orthographicChart (q+t • ξ)))) (energySecond p q ξ) 0 ∧
    hessianMargin p*‖ξ‖^2≤tau^(p+2)/p*energySecond p q ξ ∧ 0<hessianMargin p*‖ξ‖^2 :=
  ⟨energy_line_second_derivative p q ξ (convexTailDomain_norm_lt p hp q hq),
    full_hessian_strict_margin p hp q ξ hq hξ hξ0⟩

#print axioms full_hessian_assemble
end Blueprint.Thomson.Tail.Implementation
