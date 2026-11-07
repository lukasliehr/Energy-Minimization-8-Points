import AllS.Units.N_GI.N_minimizer_exists.N_outside_comparison

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem minimizer_exists_strict_separation_at_minimum (p : ℝ) (Z : Fin 8 → Point) (hp : 0 < p)
    (hZ : IsConfiguration Z) (Y : Fin 8 → Point)
    (hYK : Y ∈ separatedConfigurations (separationThreshold p Z))
    (hmin : IsMinOn (squaredEnergy p) (separatedConfigurations (separationThreshold p Z)) Y) :
    IsConfiguration Y ∧ (∀ i j, i ≠ j → separationThreshold p Z < squaredDistance Y i j) ∧
      ∀ W, IsConfiguration W → squaredEnergy p Y ≤ squaredEnergy p W := by
  obtain ⟨_,he,heq,_⟩ := minimizer_exists_separation_threshold p Z hp hZ
  have hY := separatedConfigurations_configuration _ he Y hYK
  have hZK := (minimizer_exists_compact_set p Z hp hZ).1
  have hEY : squaredEnergy p Y ≤ squaredEnergy p Z := hmin hZK
  refine ⟨hY,?_,?_⟩
  · intro i j hij
    apply (Real.rpow_lt_rpow_iff_of_neg (setup_positive_distance Y hY i j hij) he (show -p < 0 by linarith)).mp
    rw [heq]
    have ht := squaredEnergy_term_le p Y i j hij
    dsimp [separationBudget]
    linarith
  · intro W hW
    by_cases hWK : W ∈ separatedConfigurations (separationThreshold p Z)
    · exact hmin hWK
    · have hout := minimizer_exists_outside_comparison p Z hp hZ Y W hEY hW hWK
      exact (lt_trans hout.1 hout.2).le

#check minimizer_exists_strict_separation_at_minimum
#print axioms minimizer_exists_strict_separation_at_minimum
end Blueprint.Thomson.Tail.Implementation
