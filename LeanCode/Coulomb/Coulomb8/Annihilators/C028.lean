import Coulomb8.CoefficientMatrix.C03
import Coulomb8.AnnihilatorData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Annihilators.C028
open scoped BigOperators

def integers : Fin 102 → IP := ![[],[],[20480,-491520,5734400,-38338560,157982720,-395673600,589496320,-481689600,165580800],[],[-40960,835584,-8232960,48660480,-179314688,391430144,-510418944,385351680,-132464640],[],[-36864,491520,-3309568,10682368,-20357120,49774592,-100466688,96337920,-33116160],[],[90112,-1228800,7839744,-25591808,45129728,-45531136,21389312],[],[-32768,393216,-2031616,4587520,-3440640],[],[],[],[],[],[],[],[],[],[],[],[],[],[-172032,3538944,-35880960,202113024,-707051520,1577189376,-2190311424,1734082560,-596090880],[],[258048,-3981312,29024256,-106463232,190611456,-95993856,-195256320,289013760,-99348480],[],[-73728,737280,-2383872,-3440640,35266560,-60211200,30105600],[],[],[],[],[],[],[],[],[],[],[],[-98304,589824,3047424,-36569088,117669888,-152764416,68124672],[],[-98304,1179648,-6094848,13762560,-10321920],[],[],[],[],[],[],[],[],[98304,-2359296,27525120,-184025088,758317056,-1899233280,2829582336,-2312110080,794787840],[],[-196608,3538944,-29687808,137625600,-364707840,481689600,-240844800],[],[],[],[],[],[],[],[],[],[],[],[],[],[-393216,7077888,-60948480,256376832,-553254912,611057664,-272498688],[],[393216,-4718592,24379392,-55050240,41287680],[],[],[],[],[],[],[],[],[],[589824,-10616832,91422720,-384565248,829882368,-916586496,408748032],[],[-393216,4718592,-24379392,55050240,-41287680],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem scale_checked : List.ofFn CoefficientMatrix.column28=
    List.ofFn (fun r => K.scale (1/3675) (integers r).toK) := by decide +kernel

theorem checked0 : (IP.dot (List.ofFn l0) (List.ofFn integers)).isZero := by decide +kernel
theorem checked1 : (IP.dot (List.ofFn l1) (List.ofFn integers)).isZero := by decide +kernel

theorem annihilates0 : ∑ r, L0 r*K.eval (CoefficientMatrix.column28 r)=0 :=
  scaled_annihilator l0 integers _ _ 2 scale_checked checked0

theorem annihilates1 : ∑ r, L1 r*K.eval (CoefficientMatrix.column28 r)=0 := by
  simpa only [L1,div_one] using scaled_annihilator l1 integers _ _ 1 scale_checked checked1

theorem structural_zero : K.eval (CoefficientMatrix.column28 57)=0 := by rfl

end Coulomb8.Annihilators.C028
