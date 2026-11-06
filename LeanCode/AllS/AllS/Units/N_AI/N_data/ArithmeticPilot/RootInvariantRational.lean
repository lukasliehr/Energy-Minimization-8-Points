import AllS.Units.N_AI.N_data.RationalBernstein
set_option maxHeartbeats 0
set_option maxRecDepth 8192
namespace Blueprint.CAP.ArithmeticPilot.RootInvariantRational
open scoped BigOperators
def sqrtLower : Rat := 163754743014928255235102403085959256615014864942486474123643707201513509564970/2^256
def invariantUpper : Rat := 45495752179962794690739693645427246015/85070591730234615865843651857942052864
def u : Rat := (1+sqrtLower/2-1)/(1+sqrtLower/2+1)
def lowerLog : Rat := 2*∑ j∈Finset.range 41, u^(2*j+1)/((2*j+1:Nat):Rat)
def RationalGates : Prop := 0 < sqrtLower ∧ sqrtLower^2 ≤ 2 ∧ 0 ≤ u ∧ u < 1 ∧ invariantUpper ≤ lowerLog
theorem rational_gates : RationalGates := by
  unfold RationalGates
  decide +kernel
#print axioms rational_gates
end Blueprint.CAP.ArithmeticPilot.RootInvariantRational
