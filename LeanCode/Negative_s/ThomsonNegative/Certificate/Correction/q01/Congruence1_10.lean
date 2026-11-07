import ThomsonNegative.Certificate.Correction.q01.BlockData

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Compact.Packed
open ThomsonNegative.Certificate
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem congruence1_10_checked : congruenceGate context 5 ThomsonNegative.Certificate.Cells.q01.inverse1 (centerMatrix1 10)=true := by decide +kernel
theorem bound1_10_checked : allBelow 5 (fun i => allBelow 5 (fun j => Nat.beq (rangeX context (entry (congruenceTM context 5 ThomsonNegative.Certificate.Cells.q01.inverse1 (centerMatrix1 10)) i j)) (centerBound1 10 i j)))=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q01
