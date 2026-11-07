import AllS.Units.N_AI.N_data.PointLogGates
set_option maxHeartbeats 0
set_option maxRecDepth 16384
namespace Blueprint.CAP.ArithmeticPilot.base_B_21_RootLogPoint_002
def z : Rat := (2/1 : Rat)
def enclosure : Blueprint.CAP.QInterval := ⟨(40130480092995654431116952103155035266995333805794973303061433752709978488049/57896044618658097711785492504343953926634992332820282019728792003956564819968 : Rat), (10032620023248913607779238025788758816748833451448743325765358438177494622033/14474011154664524427946373126085988481658748083205070504932198000989141204992 : Rat)⟩
def Gate : Prop := enclosure.LogPointGate z (1) 76
theorem gate : Gate := by
  unfold Gate Blueprint.CAP.QInterval.LogPointGate
  decide +kernel
#print axioms gate
end Blueprint.CAP.ArithmeticPilot.base_B_21_RootLogPoint_002
