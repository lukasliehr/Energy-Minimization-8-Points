import AllS.Units.N_GI.N_trial_ceiling.N_family_minimum

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem trial_ceiling_global_minimum_ceiling (p : ℝ) (hp : (97:ℝ)/2≤p)
    (Y : Fin 8→Point)
    (hmin : ∀ Z, IsConfiguration Z → squaredEnergy p Y≤ squaredEnergy p Z) :
    tau^p*squaredEnergy p Y<(1547:ℝ)/100 := by
  have htr := trial_ceiling_trial_in_range p hp
  have hZ := Blueprint.antiprism_is_configuration (trialHeight p) ⟨htr.1,by linarith [htr.2]⟩
  exact (mul_le_mul_of_nonneg_left (hmin _ hZ) (Real.rpow_nonneg tau_pos.le p)).trans_lt
    (trial_ceiling_noncontact_trial p hp).2

#print axioms trial_ceiling_global_minimum_ceiling
end Blueprint.Thomson.Tail.Implementation
