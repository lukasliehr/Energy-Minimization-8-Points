import ThomsonNegative.Certificate.Correction.q03.BlockData

namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Compact.Packed
open ThomsonNegative.Certificate
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem congruence0_0_checked : congruenceGate context 6 ThomsonNegative.Certificate.Cells.q03.inverse0 (centerMatrix0 0)=true := by decide +kernel
theorem bound0_0_checked : allBelow 6 (fun i => allBelow 6 (fun j => Nat.beq (rangeX context (entry (congruenceTM context 6 ThomsonNegative.Certificate.Cells.q03.inverse0 (centerMatrix0 0)) i j)) (centerBound0 0 i j)))=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q03
