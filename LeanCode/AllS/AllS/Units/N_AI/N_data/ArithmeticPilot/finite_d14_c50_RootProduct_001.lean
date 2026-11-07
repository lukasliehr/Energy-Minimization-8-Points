import AllS.Units.N_AI.N_data.ScalarGates
import AllS.Units.N_AI.N_data.DiagonalProductSupport
import Mathlib.Data.Fin.VecNotation
set_option maxHeartbeats 0
set_option maxRecDepth 16384
namespace Blueprint.CAP.ArithmeticPilot.finite_d14_c50_RootProduct_001
attribute [local instance] Fintype.decidableForallFintype
def left : Blueprint.CAP.QModel 17 := ⟨![⟨(-26/1 : Rat), (-26/1 : Rat)⟩, ⟨(-3/4 : Rat), (-3/4 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩], (0/1 : Rat)⟩
def right : Blueprint.CAP.QModel 17 := ⟨![⟨(40130480092995654431116952103155035266995333805794973303061433752709978488049/57896044618658097711785492504343953926634992332820282019728792003956564819968 : Rat), (10032620023248913607779238025788758816748833451448743325765358438177494622033/14474011154664524427946373126085988481658748083205070504932198000989141204992 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩], (0/1 : Rat)⟩
def result : Blueprint.CAP.QModel 17 := ⟨![⟨(-130424060302235876901130094335253864617734834868833663234949659696307430086429/7237005577332262213973186563042994240829374041602535252466099000494570602496 : Rat), (-521696241208943507604520377341015458470939339475334652939798638785229720344637/28948022309329048855892746252171976963317496166410141009864396001978282409984 : Rat)⟩, ⟨(-30097860069746740823337714077366276450246500354346229977296075314532483866099/57896044618658097711785492504343953926634992332820282019728792003956564819968 : Rat), (-60195720139493481646675428154732552900493000708692459954592150629064967732073/115792089237316195423570985008687907853269984665640564039457584007913129639936 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩], (0/1 : Rat)⟩
def tail : Rat := (0/1 : Rat)
def Gate : Prop := left.ProductGate right result tail
theorem gate : Gate := by
  unfold Gate Blueprint.CAP.QModel.ProductGate Blueprint.CAP.qProductTailPower
    Blueprint.CAP.qProductTailControl Blueprint.CAP.qProductTailRadius
  simp only [Blueprint.CAP.qProductMid_diagonal, Blueprint.CAP.qProductRad_diagonal]
  decide +kernel
#print axioms gate
end Blueprint.CAP.ArithmeticPilot.finite_d14_c50_RootProduct_001
