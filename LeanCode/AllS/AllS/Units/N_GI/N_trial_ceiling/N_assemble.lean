import AllS.Units.N_GI.N_trial_ceiling.N_global_minimum_ceiling

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem trial_ceiling_assemble (p : ℝ) (hp : (97:ℝ)/2≤p) :
    trialHeight p∈Set.Ioo (0:ℝ) (1/3) ∧
    tau^p*squaredEnergy p (X (trialHeight p))<ceiling ∧
    (∀ h, h∈Set.Ioo (0:ℝ) 1 → F (2*p) h=0 → tau^p*squaredEnergy p (X h)<ceiling) ∧
    (∀ Y, (∀ Z, IsConfiguration Z → squaredEnergy p Y≤ squaredEnergy p Z) →
      tau^p*squaredEnergy p Y<ceiling) :=
  ⟨trial_ceiling_trial_in_range p hp,(trial_ceiling_noncontact_trial p hp).2,
    fun h hh hF=>trial_ceiling_family_minimum p h hp hh hF,
    fun Y hY=>trial_ceiling_global_minimum_ceiling p hp Y hY⟩

#print axioms trial_ceiling_assemble
end Blueprint.Thomson.Tail.Implementation
