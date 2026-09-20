import Coulomb8.EqualityContacts
import Coulomb8.ContactRigidity
import Coulomb8.EnergyInvariance

namespace Coulomb8

theorem unique_minimum (x : Configuration) (hx : Admissible x) :
    coulombEnergy x=optimalEnergy ↔ Congruent x antiprism := by
  constructor
  · intro he
    exact contact_rigidity x hx (equality_contacts x hx he)
  · intro hc
    exact (coulombEnergy_congruent x antiprism hc).trans antiprism_energy

theorem coulomb_energy_N8_global_minimizer (x : Configuration) (hx : Admissible x) :
    optimalEnergy ≤ coulombEnergy x ∧ (coulombEnergy x=optimalEnergy ↔ Congruent x antiprism) :=
  ⟨global_minimum x hx,unique_minimum x hx⟩

theorem coulomb_energy_N8_solution (x : Fin 8 → EuclideanSpace ℝ (Fin 3))
    (hunit : ∀ i, ‖x i‖=1) (hinjective : Function.Injective x) :
    coulombEnergy antiprism ≤ coulombEnergy x ∧
      (coulombEnergy x=coulombEnergy antiprism ↔
        ∃ (f : Point ≃ₗᵢ[ℝ] Point) (σ : Equiv.Perm (Fin 8)),
          ∀ i, x i=f (antiprism (σ i))) := by
  rw [antiprism_energy]
  exact coulomb_energy_N8_global_minimizer x ⟨hunit,hinjective⟩

theorem globalMinimum_verified : GlobalMinimum := global_minimum
theorem uniqueMinimum_verified : UniqueMinimum := unique_minimum

#print axioms coulomb_energy_N8_global_minimizer
#print axioms uniqueMinimum_verified
#print axioms coulomb_energy_N8_solution
end Coulomb8
