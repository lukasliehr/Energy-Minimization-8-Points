import AllS.Units.N_GI.N_full_hessian.N_assemble

noncomputable section
namespace Blueprint.Thomson.Tail
open Implementation

theorem full_hessian (p : ℝ) (hp : (97:ℝ)/2≤p) (q ξ : TangentCoordinates)
    (hq : q∈convexTailDomain p) (hξ : ξ∈rotationSlice) (hξ0 : ξ≠0) :
    HasDerivAt (deriv (fun t : ℝ=>squaredEnergy p (orthographicChart (q+t • ξ)))) (energySecond p q ξ) 0 ∧
    hessianMargin p*‖ξ‖^2≤tau^(p+2)/p*energySecond p q ξ ∧ 0<hessianMargin p*‖ξ‖^2 :=
  full_hessian_assemble p hp q ξ hq hξ hξ0

#print axioms full_hessian
end Blueprint.Thomson.Tail
