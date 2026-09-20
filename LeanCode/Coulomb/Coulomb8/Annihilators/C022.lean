import Coulomb8.CoefficientMatrix.C02
import Coulomb8.AnnihilatorData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Annihilators.C022
open scoped BigOperators

def integers : Fin 102 → IP := ![[],[],[],[],[],[],[16384,-262144,1638400,-5242880,9666560,-10747904,7143424,-2621440,409600],[98304,-1474560,8749056,-26902528,47218688,-47677440,25722880,-5734400],[131072,-1802240,10010624,-29163520,47595520,-40861696,12926976,2621440,-409600],[-98304,1474560,-8749056,26902528,-47218688,47677440,-25722880,5734400],[-147456,2064384,-11649024,34406400,-57262080,51609600,-20070400],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[-98304,1572864,-9830400,31457280,-57999360,64487424,-42860544,15728640,-2457600],[-294912,4423680,-26247168,80707584,-141656064,143032320,-77168640,17203200],[],[],[],[-884736,12386304,-69894144,206438400,-343572480,309657600,-120422400],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[98304,-1572864,9830400,-31457280,57999360,-64487424,42860544,-15728640,2457600],[294912,-4423680,26247168,-80707584,141656064,-143032320,77168640,-17203200],[],[],[],[],[884736,-12386304,69894144,-206438400,343572480,-309657600,120422400],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem scale_checked : List.ofFn CoefficientMatrix.column22=
    List.ofFn (fun r => K.scale (1/3675) (integers r).toK) := by decide +kernel

theorem checked0 : (IP.dot (List.ofFn l0) (List.ofFn integers)).isZero := by decide +kernel
theorem checked1 : (IP.dot (List.ofFn l1) (List.ofFn integers)).isZero := by decide +kernel

theorem annihilates0 : ∑ r, L0 r*K.eval (CoefficientMatrix.column22 r)=0 :=
  scaled_annihilator l0 integers _ _ 2 scale_checked checked0

theorem annihilates1 : ∑ r, L1 r*K.eval (CoefficientMatrix.column22 r)=0 := by
  simpa only [L1,div_one] using scaled_annihilator l1 integers _ _ 1 scale_checked checked1

theorem structural_zero : K.eval (CoefficientMatrix.column22 57)=0 := by rfl

end Coulomb8.Annihilators.C022
