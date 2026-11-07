import AllS.Units.N_AI.N_data.ScalarGates
import AllS.Units.N_AI.N_data.DiagonalProductSupport
import Mathlib.Data.Fin.VecNotation
set_option maxHeartbeats 0
set_option maxRecDepth 16384
namespace Blueprint.CAP.ArithmeticPilot.base_C_07_RootProduct_001
attribute [local instance] Fintype.decidableForallFintype
def left : Blueprint.CAP.QModel 15 := ⟨![⟨(-35/4 : Rat), (-35/4 : Rat)⟩, ⟨(-1/4 : Rat), (-1/4 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩], (0/1 : Rat)⟩
def right : Blueprint.CAP.QModel 15 := ⟨![⟨(40130480092995654431116952103155035266995333805794973303061433752709978488049/57896044618658097711785492504343953926634992332820282019728792003956564819968 : Rat), (10032620023248913607779238025788758816748833451448743325765358438177494622033/14474011154664524427946373126085988481658748083205070504932198000989141204992 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩], (0/1 : Rat)⟩
def result : Blueprint.CAP.QModel 15 := ⟨![⟨(-351141700813711976272273330902606558586209170800706016401787545336212311771155/57896044618658097711785492504343953926634992332820282019728792003956564819968 : Rat), (-702283401627423952544546661805213117172418341601412032803575090672424623540857/115792089237316195423570985008687907853269984665640564039457584007913129639936 : Rat)⟩, ⟨(-10032620023248913607779238025788758816748833451448743325765358438177494622033/57896044618658097711785492504343953926634992332820282019728792003956564819968 : Rat), (-2508155005812228401944809506447189704187208362862185831441339609544373655503/14474011154664524427946373126085988481658748083205070504932198000989141204992 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩], (0/1 : Rat)⟩
def tail : Rat := (0/1 : Rat)
def Gate : Prop := left.ProductGate right result tail
theorem gate : Gate := by
  unfold Gate Blueprint.CAP.QModel.ProductGate Blueprint.CAP.qProductTailPower
    Blueprint.CAP.qProductTailControl Blueprint.CAP.qProductTailRadius
  simp only [Blueprint.CAP.qProductMid_diagonal, Blueprint.CAP.qProductRad_diagonal]
  decide +kernel
#print axioms gate
end Blueprint.CAP.ArithmeticPilot.base_C_07_RootProduct_001
