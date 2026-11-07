import AllS.Units.N_AI.N_data.ScalarGates
import Mathlib.Data.Nat.Factorial.Basic

namespace Blueprint.CAP
open scoped BigOperators

def qExpTaylor (n : ℕ) (x : ℚ) : ℚ :=
  ∑ k ∈ Finset.range (n+1), x^k/(Nat.factorial k:ℚ)

def qExpUpper (n : ℕ) (x : ℚ) : ℚ :=
  qExpTaylor n x + (x^(n+1)/(Nat.factorial (n+1):ℚ))/(1-x/((n:ℚ)+2))

def QInterval.ExpPointGate (I : QInterval) (z : ℚ) (n : ℕ) : Prop :=
  |z| < (n:ℚ)+2 ∧
  if 0 ≤ z then I.lo ≤ qExpTaylor n z ∧ qExpUpper n z ≤ I.hi
  else I.lo ≤ 1/qExpUpper n (-z) ∧ 1/qExpTaylor n (-z) ≤ I.hi

end Blueprint.CAP
