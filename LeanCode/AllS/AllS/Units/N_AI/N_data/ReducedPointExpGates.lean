import AllS.Units.N_AI.N_data.PointExpGates
import AllS.Units.N_AI.N_data.IntervalExpressionGates

namespace Blueprint.CAP

def QInterval.ReducedExpPointGate (R : QInterval) (z : ℚ) (r n : ℕ)
    (I : Fin (r+1) → QInterval) : Prop :=
  (I 0).ExpPointGate (z/2^r) n ∧
  (∀ j : Fin r, ((I j.castSucc).mul (I j.castSucc)).SubsetGate (I j.succ)) ∧
  (I (Fin.last r)).SubsetGate R

end Blueprint.CAP
