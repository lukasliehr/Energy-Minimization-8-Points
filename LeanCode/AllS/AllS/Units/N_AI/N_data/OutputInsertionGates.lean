import AllS.Units.N_AI.N_data.IntervalExpressionGates
import Mathlib.Data.Matrix.Basic

namespace Blueprint.CAP

def outputEntryQ {r : ℕ} (coordinates : Fin r → String × ℕ × ℕ)
    (k : Fin r) (name : String) (i j : ℕ) : ℚ :=
  if name = (coordinates k).1 ∧
    ((i = (coordinates k).2.1 ∧ j = (coordinates k).2.2) ∨
      (i = (coordinates k).2.2 ∧ j = (coordinates k).2.1)) then 1 else 0

def qOutputInsertion {r n : ℕ} (coordinates : Fin r → String × ℕ × ℕ)
    (name : String) (V : Fin r → QInterval) : Matrix (Fin n) (Fin n) QInterval :=
  fun i j => QInterval.sum fun k => (V k).scale (outputEntryQ coordinates k name i.val j.val)

def OutputInsertionGate {r n : ℕ} (coordinates : Fin r → String × ℕ × ℕ)
    (name : String) (V : Fin r → QInterval) (C : Matrix (Fin n) (Fin n) QInterval) : Prop :=
  ∀ i j, (qOutputInsertion coordinates name V i j).SubsetGate (C i j)

instance {r n : ℕ} (coordinates : Fin r → String × ℕ × ℕ)
    (name : String) (V : Fin r → QInterval) (C : Matrix (Fin n) (Fin n) QInterval) :
    Decidable (OutputInsertionGate coordinates name V C) := by
  unfold OutputInsertionGate QInterval.SubsetGate
  infer_instance

end Blueprint.CAP
