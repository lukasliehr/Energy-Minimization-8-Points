import Coulomb8.CoefficientMatrix.C09
import Coulomb8.AnnihilatorData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Annihilators.C072
open scoped BigOperators

def integers : Fin 102 → IP := ![[0,0,81,-1080,6300,-20916,42534,-51588,29664,5508,-16407,3564,2916],[0,-54,738,-4608,17316,-43104,73008,-81900,53916,-10986,-9618,5292],[9,-144,1137,-5736,19650,-46056,72730,-73624,41685,-7336,-2891],[6,6,-312,1384,-2124,-2124,14248,-25080,21174,-7178],[-35,364,-1760,5068,-9298,10836,-7376,2100,245],[-12,164,-1020,3492,-7300,9324,-6804,2156],[36,-192,460,-736,1116,-1408,916],[-24,168,-528,944,-952,392],[-8,80,-336,560,-392],[48,-176,304,-176],[],[],[16],[18,-252,1674,-6960,20052,-41736,63380,-69104,51450,-23324,4802],[6,-102,804,-3740,11376,-23688,33964,-32340,18522,-4802],[-36,384,-1944,6048,-12560,17696,-16392,8960,-2156],[],[],[-24,168,-528,944,-952,392],[],[],[],[],[],[2,-40,368,-1960,6524,-13720,18032,-13720,4802],[-12,164,-1020,3492,-7300,9324,-6804,2156],[],[],[-8,80,-336,560,-392],[],[],[],[],[72,-528,1880,-3872,4824,-3344,968],[],[],[48,-176,304,-176],[],[],[],[],[],[],[],[],[],[],[],[32],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem scale_checked : List.ofFn CoefficientMatrix.column72=
    List.ofFn (fun r => K.scale (1/64) (integers r).toK) := by decide +kernel

theorem checked0 : (IP.dot (List.ofFn l0) (List.ofFn integers)).isZero := by decide +kernel
theorem checked1 : (IP.dot (List.ofFn l1) (List.ofFn integers)).isZero := by decide +kernel

theorem annihilates0 : ∑ r, L0 r*K.eval (CoefficientMatrix.column72 r)=0 :=
  scaled_annihilator l0 integers _ _ 2 scale_checked checked0

theorem annihilates1 : ∑ r, L1 r*K.eval (CoefficientMatrix.column72 r)=0 := by
  simpa only [L1,div_one] using scaled_annihilator l1 integers _ _ 1 scale_checked checked1

theorem structural_zero : K.eval (CoefficientMatrix.column72 57)=0 := by rfl

end Coulomb8.Annihilators.C072
