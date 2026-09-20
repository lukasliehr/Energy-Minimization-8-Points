import Coulomb8.CoefficientMatrix.C03
import Coulomb8.AnnihilatorData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Annihilators.C031
open scoped BigOperators

def integers : Fin 102 → IP := ![[],[],[],[64,-960,7040,-20608,28224,-14784],[],[-256,3072,-18560,45696,-56448,29568],[],[320,-3264,16000,-29568,28224,-14784],[],[-128,1152,-4480,4480],[],[],[],[],[-192,2880,-21120,61824,-84672,44352],[],[576,-6336,34560,-75264,84672,-44352],[],[-384,3456,-13440,13440],[],[],[],[],[],[],[192,-2880,21120,-61824,84672,-44352],[],[],[],[],[],[],[],[],[-192,576,7680,-48384,84672,-44352],[],[-384,3456,-13440,13440],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[768,-11520,84480,-247296,338688,-177408],[-768,11520,-84480,247296,-338688,177408],[-768,6912,-26880,26880],[1536,-13824,53760,-53760],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem scale_checked : List.ofFn CoefficientMatrix.column31=
    List.ofFn (fun r => K.scale (1/105) (integers r).toK) := by decide +kernel

theorem checked0 : (IP.dot (List.ofFn l0) (List.ofFn integers)).isZero := by decide +kernel
theorem checked1 : (IP.dot (List.ofFn l1) (List.ofFn integers)).isZero := by decide +kernel

theorem annihilates0 : ∑ r, L0 r*K.eval (CoefficientMatrix.column31 r)=0 :=
  scaled_annihilator l0 integers _ _ 2 scale_checked checked0

theorem annihilates1 : ∑ r, L1 r*K.eval (CoefficientMatrix.column31 r)=0 := by
  simpa only [L1,div_one] using scaled_annihilator l1 integers _ _ 1 scale_checked checked1

theorem structural_zero : K.eval (CoefficientMatrix.column31 57)=0 := by rfl

end Coulomb8.Annihilators.C031
