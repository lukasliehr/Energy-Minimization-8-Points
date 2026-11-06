import ThomsonNegative.Certificate.Correction.q09.BlockData

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Compact.Packed
open ThomsonNegative.Certificate
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem congruence1_4_checked : congruenceGate context 5 ThomsonNegative.Certificate.Cells.q09.inverse1 (centerMatrix1 4)=true := by decide +kernel
theorem bound1_4_checked : allBelow 5 (fun i => allBelow 5 (fun j => Nat.beq (rangeX context (entry (congruenceTM context 5 ThomsonNegative.Certificate.Cells.q09.inverse1 (centerMatrix1 4)) i j)) (centerBound1 4 i j)))=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
