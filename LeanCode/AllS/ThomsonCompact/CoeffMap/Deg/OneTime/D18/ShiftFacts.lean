import ThomsonCompact.CoeffMap.Deg.ShiftSound
import ThomsonCompact.CoeffMap.Deg.OneTime.D18.Shift_0_700
import ThomsonCompact.CoeffMap.Deg.OneTime.D18.Shift_700_1400
import ThomsonCompact.CoeffMap.Deg.OneTime.D18.Shift_1400_2088
import ThomsonCompact.CoeffMap.Deg.OneTime.D18.ShiftDen

/-! The D18 shift facts (F2i): every record of the re-centred table `LS` has, at `y - 17/2^6`, the value of the
record of `L` at `y` (from the one-time leaves `Shift_*`, `ShiftDen`). -/

namespace ThomsonCompact.CoeffMap.Deg.OneTime.D18
open ThomsonCompact.CoeffMap.Deg

theorem shiftRec : ∀ i, i < D18.L.nRec → D18.L.recShiftOk D18.LS 17 6 i = true := by
  intro i hi
  have hn : D18.L.nRec = 2088 := rfl
  rw [hn] at hi
  rcases (show (0 ≤ i ∧ i < 700) ∨ (700 ≤ i ∧ i < 1400) ∨ (1400 ≤ i ∧ i < 2088) by omega) with h0 | h1 | h2
  · exact DegD.recShiftRange_spec _ _ shift_0_700 i h0.1 h0.2
  · exact DegD.recShiftRange_spec _ _ shift_700_1400 i h1.1 h1.2
  · exact DegD.recShiftRange_spec _ _ shift_1400_2088 i h2.1 h2.2

/-- **D18 shift facts.** -/
theorem shiftFacts : ∀ i, i < D18.L.nRec → ∀ y : ℝ,
    (D18.LS.rfRec i).value (y - (17 : ℕ) / 2 ^ 6) = (D18.L.rfRec i).value y :=
  DegD.shift_facts _ _ shiftRec shiftDen

#print axioms shiftFacts

end ThomsonCompact.CoeffMap.Deg.OneTime.D18
