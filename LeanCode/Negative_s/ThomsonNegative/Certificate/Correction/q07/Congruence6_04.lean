import ThomsonNegative.Certificate.Correction.q07.BlockData

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Compact.Packed
open ThomsonNegative.Certificate
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem congruence6_4_checked : congruenceGate context 11 ThomsonNegative.Certificate.Cells.q07.inverse6 (centerMatrix6 4)=true := by decide +kernel
theorem bound6_4_checked : allBelow 11 (fun i => allBelow 11 (fun j => Nat.beq (rangeX context (entry (congruenceTM context 11 ThomsonNegative.Certificate.Cells.q07.inverse6 (centerMatrix6 4)) i j)) (centerBound6 4 i j)))=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
