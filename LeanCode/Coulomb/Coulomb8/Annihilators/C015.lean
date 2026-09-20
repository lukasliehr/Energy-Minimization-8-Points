import Coulomb8.CoefficientMatrix.C01
import Coulomb8.AnnihilatorData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Annihilators.C015
open scoped BigOperators

def integers : Fin 102 → IP := ![[],[],[147456,-2064384,11649024,-34406400,57262080,-51609600,20070400],[],[-540672,5996544,-25804800,56688640,-71024640,51609600,-20070400],[],[655360,-5505024,16515072,-22282240,13762560],[],[-262144,1572864,-2359296],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[-884736,12386304,-69894144,206438400,-343572480,309657600,-120422400],[],[1179648,-11796480,42467328,-66846720,41287680],[],[],[],[],[],[],[],[],[],[],[],[],[],[-1572864,9437184,-14155776],[],[],[],[],[],[],[],[],[2654208,-37158912,209682432,-619315200,1030717440,-928972800,361267200],[],[-2359296,23592960,-84934656,133693440,-82575360],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[1572864,-9437184,14155776],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem scale_checked : List.ofFn CoefficientMatrix.column15=
    List.ofFn (fun r => K.scale (1/3675) (integers r).toK) := by decide +kernel

theorem checked0 : (IP.dot (List.ofFn l0) (List.ofFn integers)).isZero := by decide +kernel
theorem checked1 : (IP.dot (List.ofFn l1) (List.ofFn integers)).isZero := by decide +kernel

theorem annihilates0 : ∑ r, L0 r*K.eval (CoefficientMatrix.column15 r)=0 :=
  scaled_annihilator l0 integers _ _ 2 scale_checked checked0

theorem annihilates1 : ∑ r, L1 r*K.eval (CoefficientMatrix.column15 r)=0 := by
  simpa only [L1,div_one] using scaled_annihilator l1 integers _ _ 1 scale_checked checked1

theorem structural_zero : K.eval (CoefficientMatrix.column15 57)=0 := by rfl

end Coulomb8.Annihilators.C015
