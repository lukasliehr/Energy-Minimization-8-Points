import Coulomb8.CoefficientMatrix.C08
import Coulomb8.AnnihilatorData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Annihilators.C068
open scoped BigOperators

def integers : Fin 102 → IP := ![[0,-24,432,-3240,13488,-33480,47856,-32760,1968,7296,-1536],[8,-144,1248,-6664,22712,-48880,63616,-44024,9440,3200],[0,-24,224,-1400,6512,-18088,26880,-19592,6000],[-32,504,-3280,11800,-24176,26168,-11360,-904],[0,208,-1968,7680,-15808,17328,-8720],[40,-536,2240,-4192,3096,376],[0,-288,1792,-3872,3392],[-16,176,-304,-112],[0,128,-384],[],[],[],[],[0,-96,1232,-6960,22112,-41824,47024,-30480,10016],[-8,112,-432,344,1672,-5328,7088,-3960],[0,208,-1952,7456,-14976,16272,-8288],[0,48,-608,2240,-3616,2448],[0,-96,704,-1760,1664],[0,-32,320,-544],[],[],[],[],[],[0,0,-32,384,-960,384,224],[24,-328,1232,-1712,408,888],[],[-16,176,-304,-112],[],[],[],[],[],[0,-384,2176,-4224,3456],[],[0,128,-384],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,-96,1440,-7248,16896,-19872,12192,-4080],[16,-240,1232,-3168,4944,-4976,2448],[0,48,-576,1888,-2752,1904],[-48,608,-2240,3616,-2448],[0,-32,320,-544],[32,-320,544],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem scale_checked : List.ofFn CoefficientMatrix.column68=
    List.ofFn (fun r => K.scale (1/17) (integers r).toK) := by decide +kernel

theorem checked0 : (IP.dot (List.ofFn l0) (List.ofFn integers)).isZero := by decide +kernel
theorem checked1 : (IP.dot (List.ofFn l1) (List.ofFn integers)).isZero := by decide +kernel

theorem annihilates0 : ∑ r, L0 r*K.eval (CoefficientMatrix.column68 r)=0 :=
  scaled_annihilator l0 integers _ _ 2 scale_checked checked0

theorem annihilates1 : ∑ r, L1 r*K.eval (CoefficientMatrix.column68 r)=0 := by
  simpa only [L1,div_one] using scaled_annihilator l1 integers _ _ 1 scale_checked checked1

theorem structural_zero : K.eval (CoefficientMatrix.column68 57)=0 := by rfl

end Coulomb8.Annihilators.C068
