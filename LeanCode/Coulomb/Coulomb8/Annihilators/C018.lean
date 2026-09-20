import Coulomb8.CoefficientMatrix.C02
import Coulomb8.AnnihilatorData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Annihilators.C018
open scoped BigOperators

def integers : Fin 102 → IP := ![[],[],[],[],[-245760,4423680,-33914880,146636800,-395509760,685146112,-747536384,471367680,-132464640],[],[868352,-13139968,83099648,-292782080,640778240,-906723328,833093632,-471367680,132464640],[],[-1015808,12648448,-63340544,168427520,-259031040,221577216,-85557248],[],[393216,-3932160,14155776,-22282240,13762560],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[737280,-13271040,101744640,-439910400,1186529280,-2055438336,2242609152,-1414103040,397393920],[],[-884736,12386304,-69894144,206438400,-343572480,309657600,-120422400],[],[],[],[],[],[],[],[],[],[],[],[-1966080,27525120,-155320320,463994880,-784465920,710148096,-272498688],[],[1179648,-11796480,42467328,-66846720,41287680],[],[],[],[],[],[],[],[],[-1474560,26542080,-203489280,879820800,-2373058560,4110876672,-4485218304,2828206080,-794787840],[],[1769472,-24772608,139788288,-412876800,687144960,-619315200,240844800],[],[],[],[],[],[],[],[],[],[],[],[],[],[1966080,-27525120,155320320,-463994880,784465920,-710148096,272498688],[],[-1179648,11796480,-42467328,66846720,-41287680],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem scale_checked : List.ofFn CoefficientMatrix.column18=
    List.ofFn (fun r => K.scale (1/3675) (integers r).toK) := by decide +kernel

theorem checked0 : (IP.dot (List.ofFn l0) (List.ofFn integers)).isZero := by decide +kernel
theorem checked1 : (IP.dot (List.ofFn l1) (List.ofFn integers)).isZero := by decide +kernel

theorem annihilates0 : ∑ r, L0 r*K.eval (CoefficientMatrix.column18 r)=0 :=
  scaled_annihilator l0 integers _ _ 2 scale_checked checked0

theorem annihilates1 : ∑ r, L1 r*K.eval (CoefficientMatrix.column18 r)=0 := by
  simpa only [L1,div_one] using scaled_annihilator l1 integers _ _ 1 scale_checked checked1

theorem structural_zero : K.eval (CoefficientMatrix.column18 57)=0 := by rfl

end Coulomb8.Annihilators.C018
