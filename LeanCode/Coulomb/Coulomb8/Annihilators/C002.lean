import Coulomb8.CoefficientMatrix.C00
import Coulomb8.AnnihilatorData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Annihilators.C002
open scoped BigOperators

def integers : Fin 102 → IP := ![[6],[14],[],[14],[14],[],[],[],[],[],[],[],[],[],[],[42],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem scale_checked : List.ofFn CoefficientMatrix.column2=
    List.ofFn (fun r => K.scale (1/21) (integers r).toK) := by decide +kernel

theorem checked0 : (IP.dot (List.ofFn l0) (List.ofFn integers)).isZero := by decide +kernel
theorem checked1 : (IP.dot (List.ofFn l1) (List.ofFn integers)).isZero := by decide +kernel

theorem annihilates0 : ∑ r, L0 r*K.eval (CoefficientMatrix.column2 r)=0 :=
  scaled_annihilator l0 integers _ _ 2 scale_checked checked0

theorem annihilates1 : ∑ r, L1 r*K.eval (CoefficientMatrix.column2 r)=0 := by
  simpa only [L1,div_one] using scaled_annihilator l1 integers _ _ 1 scale_checked checked1

theorem structural_zero : K.eval (CoefficientMatrix.column2 57)=0 := by rfl

end Coulomb8.Annihilators.C002
