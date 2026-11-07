import ThomsonNegative.Certificate.Correction.q03.BlockData

namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Compact.Packed
open ThomsonNegative.Certificate
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem congruence7_7_checked : congruenceGate context 11 ThomsonNegative.Certificate.Cells.q03.inverse7 (centerMatrix7 7)=true := by decide +kernel
theorem bound7_7_checked : allBelow 11 (fun i => allBelow 11 (fun j => Nat.beq (rangeX context (entry (congruenceTM context 11 ThomsonNegative.Certificate.Cells.q03.inverse7 (centerMatrix7 7)) i j)) (centerBound7 7 i j)))=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q03
