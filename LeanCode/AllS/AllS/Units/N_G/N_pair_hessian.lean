import AllS.Units.N_GI.N_pair_hessian.N_assemble

noncomputable section
namespace Blueprint.Thomson.Tail
open Implementation

theorem pair_hessian (p : ℝ) (hp : (97:ℝ)/2≤p) (q ξ : TangentCoordinates)
    (hq : ‖q‖≤contraction/p) (i j : Fin 8) (hij : i≠j) :
    pairSecond q ξ i j≤(8:ℝ)/3*(‖tangentVector ξ i‖^2+‖tangentVector ξ j‖^2) :=
  pair_hessian_assemble p hp q ξ hq i j hij

#print axioms pair_hessian
end Blueprint.Thomson.Tail
