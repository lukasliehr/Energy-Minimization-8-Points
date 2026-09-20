import Coulomb8.CoefficientMatrix.C03
import Coulomb8.AnnihilatorData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Annihilators.C027
open scoped BigOperators

def integers : Fin 102 → IP := ![[],[],[0,-40960,245760,40960,-6389760,19046400,-20070400,7168000],[-40960,737280,-6184960,28672000,-75980800,100352000,-50176000],[0,0,-196608,557056,4063232,-14745600,16056320,-5734400],[0,-196608,2916352,-18350080,57344000,-80281600,40140800],[0,73728,-49152,-1187840,3375104,-4792320,4014080,-1433600],[73728,-933888,5300224,-14909440,22077440,-20070400,10035200],[0,-32768,0,589824,-1048576,491520],[-32768,393216,-2031616,4587520,-3440640],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,344064,-884736,-3686400,29294592,-71516160,72253440,-25804800],[172032,-2506752,17227776,-65372160,147087360,-180633600,90316800],[0,-172032,-147456,3514368,-2457600,-8478720,12042240,-4300800],[-73728,737280,-2383872,-3440640,35266560,-60211200,30105600],[],[],[],[],[],[],[-98304,1179648,-6094848,13762560,-10321920],[],[],[],[],[],[0,-196608,0,3538944,-6291456,2949120],[-98304,1179648,-6094848,13762560,-10321920],[],[],[],[],[],[],[],[],[],[0,-196608,1179648,196608,-30670848,91422720,-96337920,34406400],[-196608,3538944,-29687808,137625600,-364707840,481689600,-240844800],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,786432,0,-14155776,25165824,-11796480],[393216,-4718592,24379392,-55050240,41287680],[],[],[],[],[],[],[],[],[],[],[0,-1179648,0,21233664,-37748736,17694720],[-393216,4718592,-24379392,55050240,-41287680],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem scale_checked : List.ofFn CoefficientMatrix.column27=
    List.ofFn (fun r => K.scale (1/3675) (integers r).toK) := by decide +kernel

theorem checked0 : (IP.dot (List.ofFn l0) (List.ofFn integers)).isZero := by decide +kernel
theorem checked1 : (IP.dot (List.ofFn l1) (List.ofFn integers)).isZero := by decide +kernel

theorem annihilates0 : ∑ r, L0 r*K.eval (CoefficientMatrix.column27 r)=0 :=
  scaled_annihilator l0 integers _ _ 2 scale_checked checked0

theorem annihilates1 : ∑ r, L1 r*K.eval (CoefficientMatrix.column27 r)=0 := by
  simpa only [L1,div_one] using scaled_annihilator l1 integers _ _ 1 scale_checked checked1

theorem structural_zero : K.eval (CoefficientMatrix.column27 57)=0 := by rfl

end Coulomb8.Annihilators.C027
