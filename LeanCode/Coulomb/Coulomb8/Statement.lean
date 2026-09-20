import Coulomb8.Parameter

namespace Coulomb8

abbrev Admissible := Thomson8.Admissible
abbrev Congruent := Thomson8.Congruent

noncomputable def height : ℝ := Real.sqrt a
noncomputable def radius : ℝ := Real.sqrt (1-a)
noncomputable def antiprism : Configuration :=
  ![Thomson8.point radius 0 height,Thomson8.point 0 radius height,
    Thomson8.point (-radius) 0 height,Thomson8.point 0 (-radius) height,
    Thomson8.point (radius/q) (radius/q) (-height),
    Thomson8.point (-radius/q) (radius/q) (-height),
    Thomson8.point (-radius/q) (-radius/q) (-height),
    Thomson8.point (radius/q) (-radius/q) (-height)]

noncomputable def coulombEnergy (x : Configuration) : ℝ :=
  ∑ i : Fin 8, ∑ j ∈ Finset.univ.filter (fun j : Fin 8 => i<j), 1/‖x i-x j‖

noncomputable def optimalEnergy : ℝ := G a

def GlobalMinimum : Prop := ∀ x : Configuration, Admissible x → optimalEnergy ≤ coulombEnergy x

def UniqueMinimum : Prop := ∀ x : Configuration, Admissible x →
  (coulombEnergy x=optimalEnergy ↔ Congruent x antiprism)

end Coulomb8
