import AllS.Units.N_GI.N_minimizer_exists.N_continuous_energy

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem minimizer_exists_attained_minimum (p : ℝ) (Z : Fin 8 → Point) (hp : 0 < p)
    (hZ : IsConfiguration Z) :
    ∃ Y ∈ separatedConfigurations (separationThreshold p Z),
      IsMinOn (squaredEnergy p) (separatedConfigurations (separationThreshold p Z)) Y ∧
      squaredEnergy p Y ≤ squaredEnergy p Z := by
  obtain ⟨hZK,hK⟩ := minimizer_exists_compact_set p Z hp hZ
  obtain ⟨Y,hYK,hmin⟩ := hK.exists_isMinOn ⟨Z,hZK⟩ (minimizer_exists_continuous_energy p Z hp hZ)
  exact ⟨Y,hYK,hmin,hmin hZK⟩

#check minimizer_exists_attained_minimum
#print axioms minimizer_exists_attained_minimum
end Blueprint.Thomson.Tail.Implementation
