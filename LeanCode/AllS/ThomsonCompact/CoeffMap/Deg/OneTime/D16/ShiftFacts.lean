import ThomsonCompact.CoeffMap.Deg.ShiftSound
import ThomsonCompact.CoeffMap.Deg.OneTime.D16.Shift_0_730
import ThomsonCompact.CoeffMap.Deg.OneTime.D16.Shift_730_1450
import ThomsonCompact.CoeffMap.Deg.OneTime.D16.ShiftDen

/-! The D16 shift facts (F2i): every record of the re-centred table `LS` has, at `y - 17/2^6`, the value of the
record of `L` at `y` (from the one-time leaves `Shift_*`, `ShiftDen`). -/

namespace ThomsonCompact.CoeffMap.Deg.OneTime.D16
open ThomsonCompact.CoeffMap.Deg

theorem shiftRec : ∀ i, i < D16.L.nRec → D16.L.recShiftOk D16.LS 17 6 i = true := by
  intro i hi
  have hn : D16.L.nRec = 1450 := rfl
  rw [hn] at hi
  rcases (show (0 ≤ i ∧ i < 730) ∨ (730 ≤ i ∧ i < 1450) by omega) with h0 | h1
  · exact DegD.recShiftRange_spec _ _ shift_0_730 i h0.1 h0.2
  · exact DegD.recShiftRange_spec _ _ shift_730_1450 i h1.1 h1.2

/-- **D16 shift facts.** -/
theorem shiftFacts : ∀ i, i < D16.L.nRec → ∀ y : ℝ,
    (D16.LS.rfRec i).value (y - (17 : ℕ) / 2 ^ 6) = (D16.L.rfRec i).value y :=
  DegD.shift_facts _ _ shiftRec shiftDen

#print axioms shiftFacts

end ThomsonCompact.CoeffMap.Deg.OneTime.D16
