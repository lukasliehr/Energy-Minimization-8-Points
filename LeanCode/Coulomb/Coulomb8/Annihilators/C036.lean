import Coulomb8.CoefficientMatrix.C04
import Coulomb8.AnnihilatorData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Annihilators.C036
open scoped BigOperators

def integers : Fin 102 → IP := ![[],[-96,288,-32,-160],[96,-960,1120],[288,-864,96,480],[-288,2880,-3360],[-288,864,-96,-480],[288,-2880,3360],[96,-288,32,160],[-96,960,-1120],[],[],[],[],[1728,-5184,576,2880],[-1728,11232,-10368,-1440],[-1152,-2592,9408,-3360],[1728,-11232,10368,1440],[-864,8640,-10080],[],[],[],[],[],[],[],[2016,-14112,13728,1440],[],[],[],[],[],[],[],[-1728,17280,-20160],[288,-864,96,480],[-288,2880,-3360],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[-1728,5184,-576,-2880],[],[],[],[],[],[],[],[],[8640,-38016,22464,11520],[-6048,42336,-41184,-4320],[2592,-25920,30240],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem scale_checked : List.ofFn CoefficientMatrix.column36=
    List.ofFn (fun r => K.scale (1/105) (integers r).toK) := by decide +kernel

theorem checked0 : (IP.dot (List.ofFn l0) (List.ofFn integers)).isZero := by decide +kernel
theorem checked1 : (IP.dot (List.ofFn l1) (List.ofFn integers)).isZero := by decide +kernel

theorem annihilates0 : ∑ r, L0 r*K.eval (CoefficientMatrix.column36 r)=0 :=
  scaled_annihilator l0 integers _ _ 2 scale_checked checked0

theorem annihilates1 : ∑ r, L1 r*K.eval (CoefficientMatrix.column36 r)=0 := by
  simpa only [L1,div_one] using scaled_annihilator l1 integers _ _ 1 scale_checked checked1

theorem structural_zero : K.eval (CoefficientMatrix.column36 57)=0 := by rfl

end Coulomb8.Annihilators.C036
