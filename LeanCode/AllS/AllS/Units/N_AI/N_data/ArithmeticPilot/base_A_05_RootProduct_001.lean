import AllS.Units.N_AI.N_data.ScalarGates
import AllS.Units.N_AI.N_data.DiagonalProductSupport
import Mathlib.Data.Fin.VecNotation
set_option maxHeartbeats 0
set_option maxRecDepth 16384
namespace Blueprint.CAP.ArithmeticPilot.base_A_05_RootProduct_001
attribute [local instance] Fintype.decidableForallFintype
def left : Blueprint.CAP.QModel 17 := ⟨![⟨(-3/2 : Rat), (-3/2 : Rat)⟩, ⟨(-34737626771194858627071295502606372355980995399692169211837275202373938891981/115792089237316195423570985008687907853269984665640564039457584007913129639936 : Rat), (-8684406692798714656767823875651593088995248849923042302959318800593484722995/28948022309329048855892746252171976963317496166410141009864396001978282409984 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩], (0/1 : Rat)⟩
def right : Blueprint.CAP.QModel 17 := ⟨![⟨(40130480092995654431116952103155035266995333805794973303061433752709978488049/57896044618658097711785492504343953926634992332820282019728792003956564819968 : Rat), (10032620023248913607779238025788758816748833451448743325765358438177494622033/14474011154664524427946373126085988481658748083205070504932198000989141204992 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩], (0/1 : Rat)⟩
def result : Blueprint.CAP.QModel 17 := ⟨![⟨(-30097860069746740823337714077366276450246500354346229977296075314532483866099/28948022309329048855892746252171976963317496166410141009864396001978282409984 : Rat), (-120391440278986963293350856309465105800986001417384919909184301258129935464147/115792089237316195423570985008687907853269984665640564039457584007913129639936 : Rat)⟩, ⟨(-1504893003487337041166885703868313822512325017717311498864803765726624193305/7237005577332262213973186563042994240829374041602535252466099000494570602496 : Rat), (-6019572013949348164667542815473255290049300070869245995459215062906496773207/28948022309329048855892746252171976963317496166410141009864396001978282409984 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩], (0/1 : Rat)⟩
def tail : Rat := (0/1 : Rat)
def Gate : Prop := left.ProductGate right result tail
theorem gate : Gate := by
  unfold Gate Blueprint.CAP.QModel.ProductGate Blueprint.CAP.qProductTailPower
    Blueprint.CAP.qProductTailControl Blueprint.CAP.qProductTailRadius
  simp only [Blueprint.CAP.qProductMid_diagonal, Blueprint.CAP.qProductRad_diagonal]
  decide +kernel
#print axioms gate
end Blueprint.CAP.ArithmeticPilot.base_A_05_RootProduct_001
