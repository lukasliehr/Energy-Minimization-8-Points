import AllS.Units.N_AI.N_data.ScalarGates
import AllS.Units.N_AI.N_data.DiagonalProductSupport
import Mathlib.Data.Fin.VecNotation
set_option maxHeartbeats 0
set_option maxRecDepth 16384
namespace Blueprint.CAP.ArithmeticPilot.base_B_24_RootProduct_001
attribute [local instance] Fintype.decidableForallFintype
def left : Blueprint.CAP.QModel 15 := ⟨![⟨(-9/2 : Rat), (-9/2 : Rat)⟩, ⟨(-17368813385597429313535647751303186177990497699846084605918637601186969445991/115792089237316195423570985008687907853269984665640564039457584007913129639936 : Rat), (-8684406692798714656767823875651593088995248849923042302959318800593484722995/57896044618658097711785492504343953926634992332820282019728792003956564819968 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩], (0/1 : Rat)⟩
def right : Blueprint.CAP.QModel 15 := ⟨![⟨(40130480092995654431116952103155035266995333805794973303061433752709978488049/57896044618658097711785492504343953926634992332820282019728792003956564819968 : Rat), (10032620023248913607779238025788758816748833451448743325765358438177494622033/14474011154664524427946373126085988481658748083205070504932198000989141204992 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩], (0/1 : Rat)⟩
def result : Blueprint.CAP.QModel 15 := ⟨![⟨(-90293580209240222470013142232098829350739501063038689931888225943597451598297/28948022309329048855892746252171976963317496166410141009864396001978282409984 : Rat), (-361174320836960889880052568928395317402958004252154759727552903774389806392441/115792089237316195423570985008687907853269984665640564039457584007913129639936 : Rat)⟩, ⟨(-12039144027898696329335085630946510580098600141738491990918430125812993546441/115792089237316195423570985008687907853269984665640564039457584007913129639936 : Rat), (-6019572013949348164667542815473255290049300070869245995459215062906496773207/57896044618658097711785492504343953926634992332820282019728792003956564819968 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩, ⟨(0/1 : Rat), (0/1 : Rat)⟩], (0/1 : Rat)⟩
def tail : Rat := (0/1 : Rat)
def Gate : Prop := left.ProductGate right result tail
theorem gate : Gate := by
  unfold Gate Blueprint.CAP.QModel.ProductGate Blueprint.CAP.qProductTailPower
    Blueprint.CAP.qProductTailControl Blueprint.CAP.qProductTailRadius
  simp only [Blueprint.CAP.qProductMid_diagonal, Blueprint.CAP.qProductRad_diagonal]
  decide +kernel
#print axioms gate
end Blueprint.CAP.ArithmeticPilot.base_B_24_RootProduct_001
