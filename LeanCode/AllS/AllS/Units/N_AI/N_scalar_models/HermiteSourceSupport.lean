import AllS.Units.N_AI.N_scalar_models.PotentialSourceSupport
import AllS.Units.N_F.N_newton_hermite

noncomputable section
namespace Blueprint.CAP
open Blueprint.Thomson.Finite

def rawContactOrder : Fin 5 → Fin 5 := ![4,2,3,1,0]

theorem rawContactOrder_injective : Function.Injective rawContactOrder := by
  decide +kernel

theorem sourceContactValues_canonical (a : ℝ) (j : Fin 5) :
    sourceContactValues a j = canonicalNodes a (rawContactOrder j) := by
  fin_cases j <;> rfl

theorem sourceContactValues_injective (a : ℝ) (ha : physical a) :
    Function.Injective (sourceContactValues a) := by
  intro i j hij
  rw [sourceContactValues_canonical,sourceContactValues_canonical] at hij
  exact rawContactOrder_injective ((canonicalNodes_strictMono a ha).injective hij)

theorem sourceContactValues_ne (a : ℝ) (ha : physical a) (i j : Fin 5)
    (hij : i ≠ j) : sourceContactValues a i ≠ sourceContactValues a j :=
  (sourceContactValues_injective a ha).ne hij

#print axioms sourceContactValues_injective
#print axioms sourceContactValues_ne
end Blueprint.CAP
