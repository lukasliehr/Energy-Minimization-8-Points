import Coulomb8.CoefficientMatrix.C03
import Coulomb8.AnnihilatorData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Annihilators.C026
open scoped BigOperators

def integers : Fin 102 → IP := ![[],[640,-5760,22400,-22400],[],[0,3072,-17920,17920],[],[-1152,4224,-4480,4480],[],[512,-1536],[],[],[],[],[],[],[-2688,14976,-40320,40320],[],[1536,-4608],[],[],[],[],[],[],[],[],[1152,-1152,-13440,13440],[],[],[],[],[],[],[],[],[1536,-4608],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[3072,-27648,107520,-107520],[],[],[],[],[],[],[],[],[6144,-18432],[-6144,18432],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem scale_checked : List.ofFn CoefficientMatrix.column26=
    List.ofFn (fun r => K.scale (1/105) (integers r).toK) := by decide +kernel

theorem checked0 : (IP.dot (List.ofFn l0) (List.ofFn integers)).isZero := by decide +kernel
theorem checked1 : (IP.dot (List.ofFn l1) (List.ofFn integers)).isZero := by decide +kernel

theorem annihilates0 : ∑ r, L0 r*K.eval (CoefficientMatrix.column26 r)=0 :=
  scaled_annihilator l0 integers _ _ 2 scale_checked checked0

theorem annihilates1 : ∑ r, L1 r*K.eval (CoefficientMatrix.column26 r)=0 := by
  simpa only [L1,div_one] using scaled_annihilator l1 integers _ _ 1 scale_checked checked1

theorem structural_zero : K.eval (CoefficientMatrix.column26 57)=0 := by rfl

end Coulomb8.Annihilators.C026
