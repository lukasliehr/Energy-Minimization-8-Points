import ThomsonNegative.Certificate.Correction.q07.BlockData

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Compact.Packed
open ThomsonNegative.Certificate
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem congruence1_8_checked : congruenceGate context 5 ThomsonNegative.Certificate.Cells.q07.inverse1 (centerMatrix1 8)=true := by decide +kernel
theorem bound1_8_checked : allBelow 5 (fun i => allBelow 5 (fun j => Nat.beq (rangeX context (entry (congruenceTM context 5 ThomsonNegative.Certificate.Cells.q07.inverse1 (centerMatrix1 8)) i j)) (centerBound1 8 i j)))=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
