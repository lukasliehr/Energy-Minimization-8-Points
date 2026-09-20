import Coulomb8.CoefficientMatrix.C03
import Coulomb8.AnnihilatorData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Annihilators.C025
open scoped BigOperators

def integers : Fin 102 → IP := ![[-61440,1105920,-9277440,43008000,-113971200,150528000,-75264000],[],[253952,-3588096,23764992,-86016000,184360960,-220774400,110387200],[],[-61440,1105920,-6918144,15482880,-6164480,-10035200,5017600],[],[-163840,1179648,-3211264,4587520,-3440640],[],[65536,-393216,589824],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[-958464,8994816,-36397056,65372160,-16343040,-60211200,30105600],[],[294912,-1179648,-2555904,13762560,-10321920],[],[],[],[],[],[],[],[],[],[],[],[],[],[393216,-2359296,3538944],[],[],[],[],[],[],[],[],[-294912,5308416,-44531712,206438400,-547061760,722534400,-361267200],[],[786432,-9437184,48758784,-110100480,82575360],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[-1572864,9437184,-14155776],[],[],[],[],[],[],[],[],[],[],[],[2359296,-14155776,21233664],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem scale_checked : List.ofFn CoefficientMatrix.column25=
    List.ofFn (fun r => K.scale (1/3675) (integers r).toK) := by decide +kernel

theorem checked0 : (IP.dot (List.ofFn l0) (List.ofFn integers)).isZero := by decide +kernel
theorem checked1 : (IP.dot (List.ofFn l1) (List.ofFn integers)).isZero := by decide +kernel

theorem annihilates0 : ∑ r, L0 r*K.eval (CoefficientMatrix.column25 r)=0 :=
  scaled_annihilator l0 integers _ _ 2 scale_checked checked0

theorem annihilates1 : ∑ r, L1 r*K.eval (CoefficientMatrix.column25 r)=0 := by
  simpa only [L1,div_one] using scaled_annihilator l1 integers _ _ 1 scale_checked checked1

theorem structural_zero : K.eval (CoefficientMatrix.column25 57)=0 := by rfl

end Coulomb8.Annihilators.C025
