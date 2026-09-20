import Coulomb8.Candidate
import Mathlib.Order.WithBot

namespace Coulomb8

/-- Unordered-pair Coulomb energy, with the paper's value `+∞` at collisions. -/
noncomputable def extendedCoulombEnergy (x : Configuration) : WithTop ℝ :=
  if Function.Injective x then (coulombEnergy x : WithTop ℝ) else ⊤

theorem extendedCoulombEnergy_of_injective (x : Configuration)
    (hx : Function.Injective x) :
    extendedCoulombEnergy x=(coulombEnergy x : WithTop ℝ) := by
  simp [extendedCoulombEnergy,hx]

theorem extendedCoulombEnergy_of_collision (x : Configuration)
    (hx : ¬Function.Injective x) : extendedCoulombEnergy x=⊤ := by
  simp [extendedCoulombEnergy,hx]

theorem congruent_antiprism_injective (x : Configuration)
    (hx : Congruent x antiprism) : Function.Injective x := by
  obtain ⟨f,σ,hσ⟩ := hx
  intro i j hij
  rw [hσ i,hσ j] at hij
  exact σ.injective (antiprism_admissible.2 (f.injective hij))

theorem extended_antiprism_energy :
    extendedCoulombEnergy antiprism=(optimalEnergy : WithTop ℝ) := by
  rw [extendedCoulombEnergy_of_injective _ antiprism_admissible.2,antiprism_energy]

end Coulomb8
