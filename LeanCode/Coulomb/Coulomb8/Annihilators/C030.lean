import Coulomb8.CoefficientMatrix.C03
import Coulomb8.AnnihilatorData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Annihilators.C030
open scoped BigOperators

def integers : Fin 102 → IP := ![[],[],[],[0,-128,-384,1152,-640],[-128,1152,-4480,4480],[0,256,768,-2304,1280],[256,-2304,8960,-8960],[0,-128,-384,1152,-640],[-128,1152,-4480,4480],[],[],[],[],[],[0,384,1152,-3456,1920],[384,-3456,13440,-13440],[0,-384,-1152,3456,-1920],[-384,3456,-13440,13440],[],[],[],[],[],[],[],[0,-384,-1152,3456,-1920],[],[],[],[],[],[],[],[-768,6912,-26880,26880],[0,-384,-1152,3456,-1920],[-384,3456,-13440,13440],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,-1536,-4608,13824,-7680],[-768,8448,-22272,13056,7680],[1536,-13824,53760,-53760],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem scale_checked : List.ofFn CoefficientMatrix.column30=
    List.ofFn (fun r => K.scale (1/105) (integers r).toK) := by decide +kernel

theorem checked0 : (IP.dot (List.ofFn l0) (List.ofFn integers)).isZero := by decide +kernel
theorem checked1 : (IP.dot (List.ofFn l1) (List.ofFn integers)).isZero := by decide +kernel

theorem annihilates0 : ∑ r, L0 r*K.eval (CoefficientMatrix.column30 r)=0 :=
  scaled_annihilator l0 integers _ _ 2 scale_checked checked0

theorem annihilates1 : ∑ r, L1 r*K.eval (CoefficientMatrix.column30 r)=0 := by
  simpa only [L1,div_one] using scaled_annihilator l1 integers _ _ 1 scale_checked checked1

theorem structural_zero : K.eval (CoefficientMatrix.column30 57)=0 := by rfl

end Coulomb8.Annihilators.C030
