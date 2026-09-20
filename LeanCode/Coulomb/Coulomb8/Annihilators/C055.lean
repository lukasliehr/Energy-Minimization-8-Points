import Coulomb8.CoefficientMatrix.C06
import Coulomb8.AnnihilatorData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Annihilators.C055
open scoped BigOperators

def integers : Fin 102 → IP := ![[0,24,-408,2832,-10656,22824,-25032,7728,5760,-1536],[-8,144,-1240,6368,-19896,36592,-35368,11232,3712],[-8,160,-1208,5472,-16072,27984,-23736,5616],[24,-304,1528,-3744,2760,4688,-6744],[24,-488,2880,-7648,9000,-2744],[-16,32,672,-2784,3120],[-16,304,-816,272],[0,128,-384],[],[],[],[],[],[0,96,-1232,6816,-20160,32288,-25264,6688],[8,-64,-120,2304,-8168,12480,-7464],[0,-144,1088,-2976,3264,-720],[0,-128,1056,-2624,2208],[0,-32,320,-544],[],[],[],[],[],[],[16,-240,1120,-2336,1680,784],[-16,128,-32,-1024,1456],[-16,176,-304,-112],[],[],[],[],[],[],[0,256,-1024,768],[0,128,-384],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,96,-1392,6528,-13248,11232,-2448],[-16,256,-1440,3904,-5456,3264],[-16,192,-672,1344,-1360],[32,-384,1184,-1088],[32,-320,544],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem scale_checked : List.ofFn CoefficientMatrix.column55=
    List.ofFn (fun r => K.scale (1/17) (integers r).toK) := by decide +kernel

theorem checked0 : (IP.dot (List.ofFn l0) (List.ofFn integers)).isZero := by decide +kernel
theorem checked1 : (IP.dot (List.ofFn l1) (List.ofFn integers)).isZero := by decide +kernel

theorem annihilates0 : ∑ r, L0 r*K.eval (CoefficientMatrix.column55 r)=0 :=
  scaled_annihilator l0 integers _ _ 2 scale_checked checked0

theorem annihilates1 : ∑ r, L1 r*K.eval (CoefficientMatrix.column55 r)=0 := by
  simpa only [L1,div_one] using scaled_annihilator l1 integers _ _ 1 scale_checked checked1

theorem structural_zero : K.eval (CoefficientMatrix.column55 57)=0 := by rfl

end Coulomb8.Annihilators.C055
