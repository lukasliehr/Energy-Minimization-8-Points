import Coulomb8.CoefficientMatrix.C10
import Coulomb8.AnnihilatorData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Annihilators.C080
open scoped BigOperators

def integers : Fin 102 → IP := ![[0,36,-708,5988,-29148,89604,-176796,214428,-134916,9432,32064,-6912],[-12,240,-2328,14080,-56400,151968,-273000,312064,-197860,38128,16192],[-4,128,-1336,8280,-34672,97496,-177400,197272,-117980,25144],[36,-592,4096,-15792,35160,-40656,9600,29200,-24124],[4,-324,3228,-14412,35692,-51180,40244,-12484],[-24,320,-1160,960,3032,-7680,5320],[16,-16,-272,848,-1664,1600],[0,-96,704,-1760,1664],[-16,176,-304,-112],[0,128,-384],[],[],[],[0,144,-2136,14400,-57096,144256,-236616,244384,-142296,33424],[12,-168,592,936,-12872,42952,-74960,70392,-28420],[0,-232,2384,-10280,24224,-33176,25040,-7192],[0,-48,656,-2880,6208,-6928,2992],[],[0,-96,704,-1760,1664],[0,-32,320,-544],[],[],[],[],[8,-168,1368,-5720,12376,-12600,3528,2744],[-24,320,-1160,960,3032,-7680,5320],[],[],[-16,176,-304,-112],[],[],[],[],[0,384,-2560,6656,-8704,4224],[],[],[0,128,-384],[],[],[],[],[],[],[],[],[],[],[],[],[0,144,-2424,15072,-48696,91728,-102120,60480,-12648],[-24,416,-2776,10352,-24648,37664,-33544,13328],[-8,112,-616,2400,-5496,6512,-3672],[48,-656,2880,-6208,6928,-2992],[],[0,-32,320,-544],[32,-320,544],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem scale_checked : List.ofFn CoefficientMatrix.column80=
    List.ofFn (fun r => K.scale (1/17) (integers r).toK) := by decide +kernel

theorem checked0 : (IP.dot (List.ofFn l0) (List.ofFn integers)).isZero := by decide +kernel
theorem checked1 : (IP.dot (List.ofFn l1) (List.ofFn integers)).isZero := by decide +kernel

theorem annihilates0 : ∑ r, L0 r*K.eval (CoefficientMatrix.column80 r)=0 :=
  scaled_annihilator l0 integers _ _ 2 scale_checked checked0

theorem annihilates1 : ∑ r, L1 r*K.eval (CoefficientMatrix.column80 r)=0 := by
  simpa only [L1,div_one] using scaled_annihilator l1 integers _ _ 1 scale_checked checked1

theorem structural_zero : K.eval (CoefficientMatrix.column80 57)=0 := by rfl

end Coulomb8.Annihilators.C080
