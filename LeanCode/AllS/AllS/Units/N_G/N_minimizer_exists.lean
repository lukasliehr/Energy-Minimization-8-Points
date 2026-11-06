import AllS.Units.N_GI.N_minimizer_exists.N_assemble

noncomputable section
namespace Blueprint.Thomson.Tail
open Implementation

theorem minimizer_exists (p : ℝ) (Z : Fin 8 → Point) (hp : 0 < p)
    (hZ : IsConfiguration Z) :
    ∃ Y, IsConfiguration Y ∧ Stationary p Y ∧
      squaredEnergy p Y ≤ squaredEnergy p Z ∧
      (∀ W, IsConfiguration W → squaredEnergy p Y ≤ squaredEnergy p W) ∧
      Y ∈ separatedConfigurations (separationThreshold p Z) ∧
      IsMinOn (squaredEnergy p) (separatedConfigurations (separationThreshold p Z)) Y ∧
      (∀ i j, i ≠ j → separationThreshold p Z < squaredDistance Y i j) :=
  minimizer_exists_assemble p Z hp hZ

#check minimizer_exists
#print axioms minimizer_exists
end Blueprint.Thomson.Tail
