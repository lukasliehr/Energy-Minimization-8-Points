import AllS.Units.N_GI.N_minimizer_exists.N_stationarity

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem minimizer_exists_assemble (p : ℝ) (Z : Fin 8 → Point) (hp : 0 < p)
    (hZ : IsConfiguration Z) :
    ∃ Y, IsConfiguration Y ∧ Stationary p Y ∧
      squaredEnergy p Y ≤ squaredEnergy p Z ∧
      (∀ W, IsConfiguration W → squaredEnergy p Y ≤ squaredEnergy p W) ∧
      Y ∈ separatedConfigurations (separationThreshold p Z) ∧
      IsMinOn (squaredEnergy p) (separatedConfigurations (separationThreshold p Z)) Y ∧
      (∀ i j, i ≠ j → separationThreshold p Z < squaredDistance Y i j) := by
  obtain ⟨Y,hYK,hmin,hYZ⟩ := minimizer_exists_attained_minimum p Z hp hZ
  obtain ⟨hY,hsep,hglobal⟩ :=
    minimizer_exists_strict_separation_at_minimum p Z hp hZ Y hYK hmin
  exact ⟨Y,hY,minimizer_exists_stationarity p Y hY hglobal,hYZ,hglobal,hYK,hmin,hsep⟩

#check minimizer_exists_assemble
#print axioms minimizer_exists_assemble
end Blueprint.Thomson.Tail.Implementation
