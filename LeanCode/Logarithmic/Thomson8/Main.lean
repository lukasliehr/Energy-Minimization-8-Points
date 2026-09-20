import Thomson8.UniqueMinimum
import Mathlib.Data.EReal.Basic

namespace Thomson8

/-- The paper's convention: coincident points have energy positive infinity. -/
noncomputable def extendedLogEnergy (x : Configuration) : EReal :=
  if Function.Injective x then (logEnergy x : EReal) else ⊤

theorem congruent_antiprism_injective (x : Configuration) (h : Congruent x antiprism) :
    Function.Injective x := by
  obtain ⟨f,σ,hσ⟩ := h
  intro i j hij
  rw [hσ i,hσ j] at hij
  exact σ.injective (antiprism_admissible.2 (f.injective hij))

/-- The unrestricted energy theorem, including the convention for collisions. -/
theorem full_global_minimum (x : Configuration) (hx : ∀ i, ‖x i‖=1) :
    (optimalEnergy : EReal) ≤ extendedLogEnergy x ∧
      (extendedLogEnergy x=(optimalEnergy : EReal) ↔ Congruent x antiprism) := by
  classical
  by_cases hi : Function.Injective x
  · simp only [extendedLogEnergy,if_pos hi,EReal.coe_le_coe_iff,EReal.coe_eq_coe_iff]
    exact logarithmic_energy_N8_global_minimizer x ⟨hx,hi⟩
  · simp only [extendedLogEnergy,if_neg hi]
    refine ⟨le_top, ?_⟩
    constructor
    · intro h
      exact False.elim ((EReal.coe_ne_top optimalEnergy) h.symm)
    · intro h
      exact False.elim (hi (congruent_antiprism_injective x h))

theorem antiprism_attains_minimum :
    extendedLogEnergy antiprism=(optimalEnergy : EReal) := by
  simp only [extendedLogEnergy,if_pos antiprism_admissible.2,antiprism_energy]

#print axioms full_global_minimum
#print axioms antiprism_attains_minimum
end Thomson8
