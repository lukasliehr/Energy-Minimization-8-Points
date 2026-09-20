import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt

namespace Thomson8

abbrev Point := EuclideanSpace ℝ (Fin 3)
abbrev Configuration := Fin 8 → Point

noncomputable def a : ℝ := (2 * Real.sqrt 58 - 13) / 7
noncomputable def height : ℝ := Real.sqrt a
noncomputable def radius : ℝ := Real.sqrt (1-a)

noncomputable def point (x y z : ℝ) : Point := WithLp.toLp 2 ![x,y,z]

noncomputable def antiprism : Configuration :=
  ![point radius 0 height, point 0 radius height,
    point (-radius) 0 height, point 0 (-radius) height,
    point (radius / Real.sqrt 2) (radius / Real.sqrt 2) (-height),
    point (-radius / Real.sqrt 2) (radius / Real.sqrt 2) (-height),
    point (-radius / Real.sqrt 2) (-radius / Real.sqrt 2) (-height),
    point (radius / Real.sqrt 2) (-radius / Real.sqrt 2) (-height)]

def Admissible (x : Configuration) : Prop :=
  (∀ i, ‖x i‖=1) ∧ Function.Injective x

noncomputable def logEnergy (x : Configuration) : ℝ :=
  ∑ i : Fin 8, ∑ j ∈ Finset.univ.filter (fun j : Fin 8 => i < j),
    -Real.log ‖x i-x j‖

noncomputable def optimalEnergy : ℝ :=
  -12*Real.log 2-6*Real.log (1-a)-4*Real.log (1+6*a+a^2)

def Congruent (x y : Configuration) : Prop :=
  ∃ (f : Point ≃ₗᵢ[ℝ] Point) (σ : Equiv.Perm (Fin 8)), ∀ i, x i=f (y (σ i))

/- These definitions specify the proof targets. They are not assertions that
the targets have already been proved. -/
def GlobalMinimum : Prop := ∀ x : Configuration, Admissible x → optimalEnergy ≤ logEnergy x
def UniqueMinimum : Prop := ∀ x : Configuration, Admissible x →
  (logEnergy x = optimalEnergy ↔ Congruent x antiprism)

end Thomson8
