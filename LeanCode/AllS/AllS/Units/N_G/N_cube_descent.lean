import AllS.Units.N_GI.N_cube_descent.N_assemble

namespace Blueprint.Thomson.Tail
open Implementation

theorem cube_descent (c : ℝ) (q : Fin 3 → ℝ) (h : CubeFeasible c q) (hc : c<7/25) :
    CubeAntiprismParameters c q ∨ (CubeDescentCurve c q ∧ HasCubeDescent c q) :=
  cube_descent_assemble c q h hc

#print axioms cube_descent
end Blueprint.Thomson.Tail
