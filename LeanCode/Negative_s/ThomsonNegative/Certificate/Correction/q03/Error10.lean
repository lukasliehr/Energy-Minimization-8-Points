import ThomsonNegative.Certificate.Correction.q03.BlockData

namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Certificate
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem rawError40_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 40 j))=rawError 40 := by decide +kernel
theorem rawError41_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 41 j))=rawError 41 := by decide +kernel
theorem rawError42_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 42 j))=rawError 42 := by decide +kernel
theorem rawError43_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 43 j))=rawError 43 := by decide +kernel
end ThomsonNegative.Certificate.Correction.q03
