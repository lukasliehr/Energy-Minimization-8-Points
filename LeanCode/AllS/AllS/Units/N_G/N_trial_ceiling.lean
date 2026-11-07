import AllS.Units.N_GI.N_trial_ceiling.N_assemble

noncomputable section
namespace Blueprint.Thomson.Tail
open Implementation

theorem trial_ceiling (p : ℝ) (hp : pStart≤p) :
    trialHeight p∈Set.Ioo (0:ℝ) (1/3) ∧
    tau^p*squaredEnergy p (X (trialHeight p))<ceiling ∧
    (∀ h, h∈Set.Ioo (0:ℝ) 1 → F (2*p) h=0 → tau^p*squaredEnergy p (X h)<ceiling) ∧
    (∀ Y, (∀ Z, IsConfiguration Z → squaredEnergy p Y≤ squaredEnergy p Z) →
      tau^p*squaredEnergy p Y<ceiling) := trial_ceiling_assemble p hp

#print axioms trial_ceiling
end Blueprint.Thomson.Tail
