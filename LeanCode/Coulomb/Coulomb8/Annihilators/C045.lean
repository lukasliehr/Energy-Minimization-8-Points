import Coulomb8.CoefficientMatrix.C05
import Coulomb8.AnnihilatorData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Annihilators.C045
open scoped BigOperators

def integers : Fin 102 → IP := ![[0,0,9,-72,198,-180,-63,108,36],[0,-6,54,-192,324,-222,-18,60],[1,-16,91,-256,359,-168,-59],[2,-6,12,-68,154,-94],[-3,28,-74,36,53],[-8,40,-80,48],[0,8,-24],[8,-8],[4],[],[],[],[],[2,-20,86,-200,262,-180,50],[2,-18,72,-152,166,-70],[-4,24,-56,56,-20],[-4,20,-36,20],[],[],[],[],[],[],[],[2,-16,60,-112,98],[-4,20,-44,28],[-4,16,-28],[],[],[],[],[],[],[8,-16,8],[8,-8],[],[],[],[],[],[8],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem scale_checked : List.ofFn CoefficientMatrix.column45=
    List.ofFn (fun r => K.scale (1/16) (integers r).toK) := by decide +kernel

theorem checked0 : (IP.dot (List.ofFn l0) (List.ofFn integers)).isZero := by decide +kernel
theorem checked1 : (IP.dot (List.ofFn l1) (List.ofFn integers)).isZero := by decide +kernel

theorem annihilates0 : ∑ r, L0 r*K.eval (CoefficientMatrix.column45 r)=0 :=
  scaled_annihilator l0 integers _ _ 2 scale_checked checked0

theorem annihilates1 : ∑ r, L1 r*K.eval (CoefficientMatrix.column45 r)=0 := by
  simpa only [L1,div_one] using scaled_annihilator l1 integers _ _ 1 scale_checked checked1

theorem structural_zero : K.eval (CoefficientMatrix.column45 57)=0 := by rfl

end Coulomb8.Annihilators.C045
