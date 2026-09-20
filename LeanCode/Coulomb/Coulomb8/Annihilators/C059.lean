import Coulomb8.CoefficientMatrix.C07
import Coulomb8.AnnihilatorData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Annihilators.C059
open scoped BigOperators

def integers : Fin 102 → IP := ![[0,0,9,-90,351,-648,495,54,-243,36,36],[0,-6,60,-252,582,-810,672,-240,-90,84],[1,-10,45,-134,296,-434,357,-142,25],[0,18,-134,396,-564,306,114,-136],[-6,46,-158,316,-394,302,-122],[0,-12,48,-40,-56,60],[13,-68,158,-188,109],[0,0,8,-8],[-12,32,-36],[],[4],[],[],[2,-20,90,-244,448,-580,522,-308,98],[0,0,4,-24,60,-84,72,-28],[-6,46,-158,316,-398,310,-126],[],[4,-20,40,-44,28],[],[],[],[],[],[],[0,0,0,0,8,-16,8],[0,0,-12,44,-68,36],[],[0,0,8,-8],[],[],[],[],[],[18,-96,236,-288,162],[],[-12,32,-36],[],[],[],[],[],[],[],[],[],[8],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem scale_checked : List.ofFn CoefficientMatrix.column59=
    List.ofFn (fun r => K.scale (1/16) (integers r).toK) := by decide +kernel

theorem checked0 : (IP.dot (List.ofFn l0) (List.ofFn integers)).isZero := by decide +kernel
theorem checked1 : (IP.dot (List.ofFn l1) (List.ofFn integers)).isZero := by decide +kernel

theorem annihilates0 : ∑ r, L0 r*K.eval (CoefficientMatrix.column59 r)=0 :=
  scaled_annihilator l0 integers _ _ 2 scale_checked checked0

theorem annihilates1 : ∑ r, L1 r*K.eval (CoefficientMatrix.column59 r)=0 := by
  simpa only [L1,div_one] using scaled_annihilator l1 integers _ _ 1 scale_checked checked1

theorem structural_zero : K.eval (CoefficientMatrix.column59 57)=0 := by rfl

end Coulomb8.Annihilators.C059
