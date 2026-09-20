import Thomson8.EqualityContacts
import Thomson8.ContactRigidity
import Thomson8.EnergyInvariance

namespace Thomson8

theorem unique_minimum (x : Configuration) (hx : Admissible x) :
    logEnergy x=optimalEnergy ↔ Congruent x antiprism := by
  constructor
  · intro he
    exact contact_rigidity x hx (equality_contacts x hx he)
  · intro hc
    exact (logEnergy_congruent x antiprism hc).trans antiprism_energy

theorem logarithmic_energy_N8_global_minimizer (x : Configuration) (hx : Admissible x) :
    optimalEnergy ≤ logEnergy x ∧ (logEnergy x=optimalEnergy ↔ Congruent x antiprism) :=
  ⟨global_minimum x hx,unique_minimum x hx⟩

theorem globalMinimum_verified : GlobalMinimum := global_minimum
theorem uniqueMinimum_verified : UniqueMinimum := unique_minimum

#print axioms logarithmic_energy_N8_global_minimizer
#print axioms uniqueMinimum_verified
end Thomson8
