import Coulomb8.CoefficientMatrix.C02
import Coulomb8.AnnihilatorData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Annihilators.C017
open scoped BigOperators

def integers : Fin 102 → IP := ![[],[],[],[],[98304,-1474560,8749056,-26902528,47218688,-47677440,25722880,-5734400],[294912,-4128768,23298048,-68812800,114524160,-103219200,40140800],[-229376,2916352,-14254080,36077568,-54165504,49643520,-25722880,5734400],[-688128,8060928,-37453824,91095040,-128286720,103219200,-40140800],[131072,-1441792,5505024,-9175040,6946816,-1966080],[393216,-3932160,14155776,-22282240,13762560],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[-294912,4423680,-26247168,80707584,-141656064,143032320,-77168640,17203200],[-884736,12386304,-69894144,206438400,-343572480,309657600,-120422400],[],[],[],[],[],[],[],[],[],[],[],[],[786432,-8650752,33030144,-55050240,41680896,-11796480],[1179648,-11796480,42467328,-66846720,41287680],[],[],[],[],[],[],[],[],[],[589824,-8847360,52494336,-161415168,283312128,-286064640,154337280,-34406400],[1769472,-24772608,139788288,-412876800,687144960,-619315200,240844800],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[-786432,8650752,-33030144,55050240,-41680896,11796480],[-1179648,11796480,-42467328,66846720,-41287680],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem scale_checked : List.ofFn CoefficientMatrix.column17=
    List.ofFn (fun r => K.scale (1/3675) (integers r).toK) := by decide +kernel

theorem checked0 : (IP.dot (List.ofFn l0) (List.ofFn integers)).isZero := by decide +kernel
theorem checked1 : (IP.dot (List.ofFn l1) (List.ofFn integers)).isZero := by decide +kernel

theorem annihilates0 : ∑ r, L0 r*K.eval (CoefficientMatrix.column17 r)=0 :=
  scaled_annihilator l0 integers _ _ 2 scale_checked checked0

theorem annihilates1 : ∑ r, L1 r*K.eval (CoefficientMatrix.column17 r)=0 := by
  simpa only [L1,div_one] using scaled_annihilator l1 integers _ _ 1 scale_checked checked1

theorem structural_zero : K.eval (CoefficientMatrix.column17 57)=0 := by rfl

end Coulomb8.Annihilators.C017
