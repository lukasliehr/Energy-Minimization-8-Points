import Coulomb8.CoefficientMatrix.C04
import Coulomb8.AnnihilatorData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Annihilators.C037
open scoped BigOperators

def integers : Fin 102 → IP := ![[],[-48,800,-3360,6048,-3696],[],[240,-3360,11200,-18144,11088],[],[-432,5280,-13440,18144,-11088],[],[336,-3680,6720,-6048,3696],[],[-96,960,-1120],[],[],[],[864,-14400,60480,-108864,66528],[-432,7200,-30240,54432,-33264],[-1872,25440,-80640,127008,-77616],[1296,-15840,40320,-54432,33264],[864,-8640,10080],[-864,8640,-10080],[],[],[],[],[],[],[432,-7200,30240,-54432,33264],[],[],[],[],[],[],[],[2304,-23040,26880],[-720,6240,0,-18144,11088],[],[-288,2880,-3360],[],[],[],[],[],[],[],[],[],[],[],[],[],[-864,14400,-60480,108864,-66528],[],[],[],[],[],[],[],[],[3456,-57600,241920,-435456,266112],[-432,12960,-80640,163296,-99792],[-3456,34560,-40320],[2592,-25920,30240],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem scale_checked : List.ofFn CoefficientMatrix.column37=
    List.ofFn (fun r => K.scale (1/105) (integers r).toK) := by decide +kernel

theorem checked0 : (IP.dot (List.ofFn l0) (List.ofFn integers)).isZero := by decide +kernel
theorem checked1 : (IP.dot (List.ofFn l1) (List.ofFn integers)).isZero := by decide +kernel

theorem annihilates0 : ∑ r, L0 r*K.eval (CoefficientMatrix.column37 r)=0 :=
  scaled_annihilator l0 integers _ _ 2 scale_checked checked0

theorem annihilates1 : ∑ r, L1 r*K.eval (CoefficientMatrix.column37 r)=0 := by
  simpa only [L1,div_one] using scaled_annihilator l1 integers _ _ 1 scale_checked checked1

theorem structural_zero : K.eval (CoefficientMatrix.column37 57)=0 := by rfl

end Coulomb8.Annihilators.C037
