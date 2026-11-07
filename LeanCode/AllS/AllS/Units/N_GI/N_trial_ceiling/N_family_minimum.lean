import AllS.Units.N_GI.N_trial_ceiling.N_noncontact_trial

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem trial_ceiling_family_minimum (p h : ℝ) (hp : (97:ℝ)/2≤p)
    (hh : h∈Set.Ioo (0:ℝ) 1) (hF : F (2*p) h=0) :
    tau^p*squaredEnergy p (X h)<(1547:ℝ)/100 := by
  have hp0 : 0<2*p := by linarith
  have heq := SquareAntiprismVerification.aStar_unique (2*p) hp0.le h hh hF
  have htr := trial_ceiling_trial_in_range p hp
  have htr' : trialHeight p∈Set.Ioo (0:ℝ) 1 := ⟨htr.1,by linarith [htr.2]⟩
  have hmin := (SquareAntiprismVerification.aStar_family_minimizer (2*p) hp0 (trialHeight p) htr').1
  have he : squaredEnergy p (X h)≤ squaredEnergy p (X (trialHeight p)) := by
    rw [trial_energy_formula p h hh,trial_energy_formula p _ htr',heq]
    exact hmin
  exact (mul_le_mul_of_nonneg_left he (Real.rpow_nonneg tau_pos.le p)).trans_lt
    (trial_ceiling_noncontact_trial p hp).2

#print axioms trial_ceiling_family_minimum
end Blueprint.Thomson.Tail.Implementation
