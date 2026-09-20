import Coulomb8.CoefficientMatrix.C03
import Coulomb8.AnnihilatorData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Annihilators.C024
open scoped BigOperators

def integers : Fin 102 → IP := ![[],[],[],[],[],[],[102400,-2252800,21811200,-123699200,458956800,-1169244160,2076712960,-2542632960,2056212480,-993484800,218566656],[],[-348160,6676480,-55726080,270336000,-854466560,1854390272,-2824249344,3014000640,-2188677120,993484800,-218566656],[],[393216,-6488064,45563904,-181043200,452771840,-736755712,767606784,-471367680,132464640],[],[-147456,2064384,-11649024,34406400,-57262080,51609600,-20070400],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[-614400,13516800,-130867200,742195200,-2753740800,7015464960,-12460277760,15255797760,-12337274880,5960908800,-1311399936],[],[737280,-13271040,101744640,-439910400,1186529280,-2055438336,2242609152,-1414103040,397393920],[],[],[],[],[],[-884736,12386304,-69894144,206438400,-343572480,309657600,-120422400],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[614400,-13516800,130867200,-742195200,2753740800,-7015464960,12460277760,-15255797760,12337274880,-5960908800,1311399936],[],[-737280,13271040,-101744640,439910400,-1186529280,2055438336,-2242609152,1414103040,-397393920],[],[],[],[],[],[],[],[884736,-12386304,69894144,-206438400,343572480,-309657600,120422400],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem scale_checked : List.ofFn CoefficientMatrix.column24=
    List.ofFn (fun r => K.scale (1/3675) (integers r).toK) := by decide +kernel

theorem checked0 : (IP.dot (List.ofFn l0) (List.ofFn integers)).isZero := by decide +kernel
theorem checked1 : (IP.dot (List.ofFn l1) (List.ofFn integers)).isZero := by decide +kernel

theorem annihilates0 : ∑ r, L0 r*K.eval (CoefficientMatrix.column24 r)=0 :=
  scaled_annihilator l0 integers _ _ 2 scale_checked checked0

theorem annihilates1 : ∑ r, L1 r*K.eval (CoefficientMatrix.column24 r)=0 := by
  simpa only [L1,div_one] using scaled_annihilator l1 integers _ _ 1 scale_checked checked1

theorem structural_zero : K.eval (CoefficientMatrix.column24 57)=0 := by rfl

end Coulomb8.Annihilators.C024
