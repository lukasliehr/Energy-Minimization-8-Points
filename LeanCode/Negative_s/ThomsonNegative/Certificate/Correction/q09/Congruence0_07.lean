import ThomsonNegative.Certificate.Correction.q09.BlockData

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Compact.Packed
open ThomsonNegative.Certificate
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem congruence0_7_checked : congruenceGate context 6 ThomsonNegative.Certificate.Cells.q09.inverse0 (centerMatrix0 7)=true := by decide +kernel
theorem bound0_7_checked : allBelow 6 (fun i => allBelow 6 (fun j => Nat.beq (rangeX context (entry (congruenceTM context 6 ThomsonNegative.Certificate.Cells.q09.inverse0 (centerMatrix0 7)) i j)) (centerBound0 7 i j)))=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
