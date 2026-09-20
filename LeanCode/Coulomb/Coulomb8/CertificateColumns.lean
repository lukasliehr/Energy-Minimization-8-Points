import Coulomb8.ColumnEvaluation

namespace Coulomb8
open scoped BigOperators

theorem certificate_identity (w : Fin 192 → ℝ)
    (hw : ∀ r, ∑ c, CoefficientMatrix.matrix r c*w c=target r) (u v t : ℝ) :
    certificateValue w u v t=(H u+H v+H t)/3-G a/28 := by
  rw [certificateValue_columns]
  simp_rw [certificateColumn_eval]
  calc
    _ = realExpansion (fun r => ∑ c, CoefficientMatrix.matrix r c*w c) u v t :=
      (expansion_sum (fun r c => CoefficientMatrix.matrix r c) w u v t).symm
    _ = realExpansion target u v t :=
      congrArg (fun f : Fin 102 → ℝ => realExpansion f u v t) (funext hw)
    _ = (H u+H v+H t)/3-G a/28 := target_expansion u v t

end Coulomb8

#print axioms Coulomb8.certificate_identity
