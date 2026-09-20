import Coulomb8.BlockMatrix
import Coulomb8.FinitePositivity

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.PSDBounds.F5

def preconditioner : Matrix (Fin 1) (Fin 1) ℤ := ![![12569585756683]]
def boxes : Fin 1 → Fin 1 → Dyadic := ![![⟨2603737315797188491672178992621813760,2603737318273068570242939542420062208⟩]]

theorem contains (w : Fin 192 → ℝ)
    (h : ∀ c, |w c-Witness.center c| ≤ (correctionRadius : ℝ))
    (i j : Fin 1) : (boxes i j).Contains (Data.F5.matrixFrom w i j) := by
  fin_cases i <;> fin_cases j
  · exact centerBox_contains w h 44

theorem checked0_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 1) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem positive (w : Fin 192 → ℝ)
    (h : ∀ c, |w c-Witness.center c| ≤ (correctionRadius : ℝ)) :
    (Data.F5.matrixFrom w).PosDef := by
  apply posDef_of_entry_bounds (Dyadic.scaledMatrix preconditioner) _ (by decide)
    (Data.F5.matrixFrom_symm w)
  intro i j
  apply Dyadic.congruence_entry_bound _ _ boxes (contains w h)
  fin_cases i <;> fin_cases j
  · exact checked0_0

end Coulomb8.PSDBounds.F5

#print axioms Coulomb8.PSDBounds.F5.positive
