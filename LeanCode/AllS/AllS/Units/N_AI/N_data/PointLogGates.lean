import AllS.Units.N_AI.N_data.ScalarGates

namespace Blueprint.CAP
open scoped BigOperators

def qLogLower (n : ℕ) (v : ℚ) : ℚ :=
  2 * ∑ j ∈ Finset.range (n+1), ((v-1)/(v+1))^(2*j+1)/((2*j+1:ℕ):ℚ)

def qLogUpper (n : ℕ) (v : ℚ) : ℚ :=
  qLogLower n v + 2*((v-1)/(v+1))^(2*n+3)/
    (((2*n+3:ℕ):ℚ)*(1-((v-1)/(v+1))^2))

def QInterval.LogPointGate (I : QInterval) (z : ℚ) (r : ℤ) (n : ℕ) : Prop :=
  0 < z ∧ 1 ≤ z/(2:ℚ)^r ∧ z/(2:ℚ)^r ≤ 2 ∧
  I.lo ≤ qLogLower n (z/(2:ℚ)^r) +
    (if 0 ≤ r then (r:ℚ)*qLogLower n 2 else (r:ℚ)*qLogUpper n 2) ∧
  qLogUpper n (z/(2:ℚ)^r) +
    (if 0 ≤ r then (r:ℚ)*qLogUpper n 2 else (r:ℚ)*qLogLower n 2) ≤ I.hi

end Blueprint.CAP
