import Coulomb8.CoefficientMatrix.C05
import Coulomb8.AnnihilatorData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Annihilators.C046
open scoped BigOperators

def integers : Fin 102 → IP := ![[0,0,-9,81,-270,378,-117,-171,72,36],[0,6,-57,222,-450,486,-225,-42,72],[-1,13,-71,219,-399,379,-121,-19],[-1,-6,57,-124,61,106,-125],[5,-41,134,-206,141,-33],[5,-24,62,-104,93],[-8,32,-48,24],[-8,24,-32],[4,-4],[4],[],[],[],[-2,20,-88,222,-354,368,-236,70],[-1,9,-39,98,-149,133,-59],[5,-35,106,-174,157,-59],[2,-10,20,-22,14],[-2,10,-18,10],[],[],[],[],[],[],[0,0,-4,20,-44,28],[3,-20,66,-100,67],[0,0,4,-4],[-2,8,-14],[],[],[],[],[],[-12,44,-68,36],[-6,16,-18],[4,-4],[],[],[],[],[],[4],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem scale_checked : List.ofFn CoefficientMatrix.column46=
    List.ofFn (fun r => K.scale (1/8) (integers r).toK) := by decide +kernel

theorem checked0 : (IP.dot (List.ofFn l0) (List.ofFn integers)).isZero := by decide +kernel
theorem checked1 : (IP.dot (List.ofFn l1) (List.ofFn integers)).isZero := by decide +kernel

theorem annihilates0 : ∑ r, L0 r*K.eval (CoefficientMatrix.column46 r)=0 :=
  scaled_annihilator l0 integers _ _ 2 scale_checked checked0

theorem annihilates1 : ∑ r, L1 r*K.eval (CoefficientMatrix.column46 r)=0 := by
  simpa only [L1,div_one] using scaled_annihilator l1 integers _ _ 1 scale_checked checked1

theorem structural_zero : K.eval (CoefficientMatrix.column46 57)=0 := by rfl

end Coulomb8.Annihilators.C046
