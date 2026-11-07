import AllS.Units.N_GI.N_minimizer_exists.N_attained_minimum

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem minimizer_exists_outside_comparison (p : ℝ) (Z : Fin 8 → Point) (hp : 0 < p)
    (hZ : IsConfiguration Z) (Y W : Fin 8 → Point) (hY : squaredEnergy p Y ≤ squaredEnergy p Z)
    (hW : IsConfiguration W) (hWK : W ∉ separatedConfigurations (separationThreshold p Z)) :
    squaredEnergy p Y < separationBudget p Z ∧ separationBudget p Z < squaredEnergy p W := by
  obtain ⟨_,_,heq,_⟩ := minimizer_exists_separation_threshold p Z hp hZ
  have hnot : ¬∀ i j, i ≠ j → separationThreshold p Z ≤ squaredDistance W i j :=
    fun hh => hWK ⟨hW.1,hh⟩
  push_neg at hnot
  obtain ⟨i,j,hij,hd⟩ := hnot
  have ht := Real.rpow_lt_rpow_of_neg (setup_positive_distance W hW i j hij) hd (show -p < 0 by linarith)
  rw [heq] at ht
  refine ⟨?_,lt_of_lt_of_le ht (squaredEnergy_term_le p W i j hij)⟩
  dsimp [separationBudget]
  linarith

#check minimizer_exists_outside_comparison
#print axioms minimizer_exists_outside_comparison
end Blueprint.Thomson.Tail.Implementation
