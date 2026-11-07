import AllS.Units.N_GI.N_minimizer_exists.N_compact_set

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem squaredEnergy_continuousOn (p ε : ℝ) (he : 0 < ε) :
    ContinuousOn (squaredEnergy p) (separatedConfigurations ε) := by
  unfold squaredEnergy
  apply continuousOn_finset_sum
  intro i _
  apply continuousOn_finset_sum
  intro j hj
  apply (squaredDistance_continuous i j).continuousOn.rpow_const
  intro Y hY
  exact Or.inl (ne_of_gt (lt_of_lt_of_le he (hY.2 i j (ne_of_lt (Finset.mem_filter.mp hj).2))))

theorem minimizer_exists_continuous_energy (p : ℝ) (Z : Fin 8 → Point) (hp : 0 < p)
    (hZ : IsConfiguration Z) :
    ContinuousOn (squaredEnergy p) (separatedConfigurations (separationThreshold p Z)) :=
  squaredEnergy_continuousOn p _ (minimizer_exists_separation_threshold p Z hp hZ).2.1

#check minimizer_exists_continuous_energy
#print axioms minimizer_exists_continuous_energy
end Blueprint.Thomson.Tail.Implementation
