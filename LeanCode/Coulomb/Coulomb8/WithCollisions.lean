import Coulomb8.UniqueMinimum
import Coulomb8.ExtendedEnergy

namespace Coulomb8

/-- The global theorem for every unit-sphere configuration, including collisions. -/
theorem coulomb_energy_N8_solution_with_collisions
    (x : Fin 8 → EuclideanSpace ℝ (Fin 3)) (hunit : ∀ i, ‖x i‖=1) :
    (optimalEnergy : WithTop ℝ) ≤ extendedCoulombEnergy x ∧
      (extendedCoulombEnergy x=(optimalEnergy : WithTop ℝ) ↔
        ∃ (f : Point ≃ₗᵢ[ℝ] Point) (σ : Equiv.Perm (Fin 8)),
          ∀ i, x i=f (antiprism (σ i))) := by
  classical
  change (optimalEnergy : WithTop ℝ) ≤ extendedCoulombEnergy x ∧
    (extendedCoulombEnergy x=(optimalEnergy : WithTop ℝ) ↔ Congruent x antiprism)
  by_cases hi : Function.Injective x
  · rw [extendedCoulombEnergy_of_injective x hi]
    simpa only [WithTop.coe_le_coe,WithTop.coe_eq_coe] using
      coulomb_energy_N8_global_minimizer x ⟨hunit,hi⟩
  · rw [extendedCoulombEnergy_of_collision x hi]
    refine ⟨le_top, ?_⟩
    have hc : ¬Congruent x antiprism := fun h => hi (congruent_antiprism_injective x h)
    simpa only [WithTop.top_ne_coe,false_iff] using hc

end Coulomb8

#print axioms Coulomb8.coulomb_energy_N8_solution_with_collisions
