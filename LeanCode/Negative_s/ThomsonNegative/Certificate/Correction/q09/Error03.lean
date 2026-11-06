import ThomsonNegative.Certificate.Correction.q09.BlockData

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem rawError12_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 12 j))=rawError 12 := by decide +kernel
theorem rawError13_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 13 j))=rawError 13 := by decide +kernel
theorem rawError14_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 14 j))=rawError 14 := by decide +kernel
theorem rawError15_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 15 j))=rawError 15 := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
