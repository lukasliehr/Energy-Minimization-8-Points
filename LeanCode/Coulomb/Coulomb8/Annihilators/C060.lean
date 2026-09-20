import Coulomb8.CoefficientMatrix.C07
import Coulomb8.AnnihilatorData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Annihilators.C060
open scoped BigOperators

def integers : Fin 102 → IP := ![[0,0,-27,315,-1539,4023,-5805,3825,531,-2007,360,324],[0,18,-213,1116,-3405,6624,-8283,6084,-1635,-930,672],[-3,39,-246,1006,-2812,5220,-6090,4002,-1057,-59],[-1,-30,300,-1142,2232,-2058,-24,1662,-1059],[15,-139,599,-1547,2565,-2729,1733,-497],[3,-20,107,-392,881,-1076,593],[-24,144,-416,720,-744,320],[2,0,-44,96,-70],[12,-44,84,-52],[-12,32,-36],[],[8],[],[-6,72,-402,1382,-3242,5394,-6390,5250,-2744,686],[-1,15,-108,439,-1110,1845,-2028,1365,-441],[15,-139,601,-1569,2669,-2953,1971,-595],[],[-6,42,-132,236,-238,98],[4,-20,40,-44,28],[],[],[],[],[],[0,0,-4,44,-208,448,-476,196],[3,-38,227,-692,1205,-1142,485],[],[-2,20,-84,140,-98],[0,0,8,-8],[],[],[],[],[-36,228,-688,1136,-1036,396],[],[12,-44,76,-44],[-12,32,-36],[],[],[],[],[],[],[],[],[],[8],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem scale_checked : List.ofFn CoefficientMatrix.column60=
    List.ofFn (fun r => K.scale (1/16) (integers r).toK) := by decide +kernel

theorem checked0 : (IP.dot (List.ofFn l0) (List.ofFn integers)).isZero := by decide +kernel
theorem checked1 : (IP.dot (List.ofFn l1) (List.ofFn integers)).isZero := by decide +kernel

theorem annihilates0 : ∑ r, L0 r*K.eval (CoefficientMatrix.column60 r)=0 :=
  scaled_annihilator l0 integers _ _ 2 scale_checked checked0

theorem annihilates1 : ∑ r, L1 r*K.eval (CoefficientMatrix.column60 r)=0 := by
  simpa only [L1,div_one] using scaled_annihilator l1 integers _ _ 1 scale_checked checked1

theorem structural_zero : K.eval (CoefficientMatrix.column60 57)=0 := by rfl

end Coulomb8.Annihilators.C060
