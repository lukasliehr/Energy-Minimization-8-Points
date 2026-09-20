import Coulomb8.InverseBounds
import Coulomb8.PreconditionerNorm
import Coulomb8.ResidualBounds
import Coulomb8.Embedding

namespace Coulomb8
open scoped BigOperators

theorem correction_witness : ∃ z : Fin 99 → ℝ,
    InverseBounds.selectedMatrix.mulVec z=ResidualBounds.residual ∧
    ∀ j, |z j| ≤ (correctionRadius : ℝ) :=
  correction_exists_from_separate_bounds _ _ _ InverseBounds.row_bound
    preconditioner_row_norm ResidualBounds.norm_bound

theorem reduced_solution : ∃ w : Fin 192 → ℝ,
    (∀ c, |w c-Witness.center c| ≤ (correctionRadius : ℝ)) ∧
    ∀ i : Fin 99, ∑ c, CoefficientMatrix.matrix (Witness.rows i) c*w c=target (Witness.rows i) := by
  obtain ⟨z,hz,hb⟩ := correction_witness
  refine ⟨correctedVector z,correctedVector_bound z hb,?_⟩
  apply correctedVector_equation
  intro i
  exact congrFun hz i

end Coulomb8

#print axioms Coulomb8.reduced_solution
