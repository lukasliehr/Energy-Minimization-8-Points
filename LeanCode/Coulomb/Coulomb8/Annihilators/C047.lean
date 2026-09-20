import Coulomb8.CoefficientMatrix.C05
import Coulomb8.AnnihilatorData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Annihilators.C047
open scoped BigOperators

def integers : Fin 102 → IP := ![[0,0,27,-288,1251,-2772,3033,-792,-1323,684,324],[0,-18,204,-1008,2814,-4734,4560,-1788,-594,564],[3,-48,336,-1360,3388,-5072,4084,-1072,-427],[4,-12,-4,-52,572,-1572,1892,-828],[-11,104,-407,800,-737,104,243],[-14,110,-404,788,-830,350],[10,-24,-12,56,-30],[8,-24,40,-24],[-4,16,-28],[8,-8],[8],[],[],[6,-72,396,-1304,2816,-4072,3812,-2072,490],[4,-48,272,-904,1880,-2436,1820,-588],[-12,100,-376,808,-1036,724,-208],[-6,42,-132,236,-238,98],[],[-4,20,-36,20],[],[],[],[],[],[2,-28,178,-616,1246,-1372,686],[-8,68,-272,552,-592,252],[-2,20,-84,140,-98],[],[-4,16,-28],[],[],[],[],[24,-112,240,-240,88],[12,-44,76,-44],[],[8,-8],[],[],[],[],[],[8],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem scale_checked : List.ofFn CoefficientMatrix.column47=
    List.ofFn (fun r => K.scale (1/16) (integers r).toK) := by decide +kernel

theorem checked0 : (IP.dot (List.ofFn l0) (List.ofFn integers)).isZero := by decide +kernel
theorem checked1 : (IP.dot (List.ofFn l1) (List.ofFn integers)).isZero := by decide +kernel

theorem annihilates0 : ∑ r, L0 r*K.eval (CoefficientMatrix.column47 r)=0 :=
  scaled_annihilator l0 integers _ _ 2 scale_checked checked0

theorem annihilates1 : ∑ r, L1 r*K.eval (CoefficientMatrix.column47 r)=0 := by
  simpa only [L1,div_one] using scaled_annihilator l1 integers _ _ 1 scale_checked checked1

theorem structural_zero : K.eval (CoefficientMatrix.column47 57)=0 := by rfl

end Coulomb8.Annihilators.C047
