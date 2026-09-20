import Coulomb8.CoefficientMatrix.C17
import Coulomb8.AnnihilatorData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Annihilators.C140
open scoped BigOperators

def integers : Fin 102 → IP := ![[256,-6656,75520,-498688,2133760,-6134272,11782400,-14364672,9764864,-2752512,262144],[0,-3072,62464,-542720,2680832,-8248320,15967232,-18436096,10747904,-1703936],[-512,12288,-105984,421888,-691712,-552960,4181504,-6148096,2883584],[0,7168,-121856,780288,-2488320,4090880,-2812928,20480],[256,-5632,16128,150528,-938240,1845760,-1265408],[0,-4096,57344,-212992,204800,86016],[0,0,16384,-98304,147456],[],[],[],[],[],[],[0,-1024,41984,-485376,2697216,-8451072,15332352,-14966784,6094848],[0,3072,-50176,256000,-411648,-500736,2362368,-2183168],[0,1024,-46080,403456,-1370112,2036736,-1156096],[0,0,-8192,106496,-385024,417792],[],[],[],[],[],[],[],[512,-11264,82432,-227328,243200,-211968,321024],[0,-4096,57344,-212992,204800,86016],[],[],[],[],[],[],[],[0,0,32768,-196608,294912],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[1024,-23552,233472,-1349632,4858880,-10447872,12191744,-5988352],[0,-5120,87040,-559104,1894400,-3417088,2524160],[-1024,21504,-157696,485376,-644096,295936],[0,8192,-106496,385024,-417792],[],[],[],[],[],[],[0,-2048,40960,-274432,696320,-591872],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[1024,-20480,137216,-348160,295936],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem scale_checked : List.ofFn CoefficientMatrix.column140=
    List.ofFn (fun r => K.scale (1/289) (integers r).toK) := by decide +kernel

theorem checked0 : (IP.dot (List.ofFn l0) (List.ofFn integers)).isZero := by decide +kernel
theorem checked1 : (IP.dot (List.ofFn l1) (List.ofFn integers)).isZero := by decide +kernel

theorem annihilates0 : ∑ r, L0 r*K.eval (CoefficientMatrix.column140 r)=0 :=
  scaled_annihilator l0 integers _ _ 2 scale_checked checked0

theorem annihilates1 : ∑ r, L1 r*K.eval (CoefficientMatrix.column140 r)=0 := by
  simpa only [L1,div_one] using scaled_annihilator l1 integers _ _ 1 scale_checked checked1

theorem structural_zero : K.eval (CoefficientMatrix.column140 57)=0 := by rfl

end Coulomb8.Annihilators.C140
