import ThomsonNegative.Certificate.Correction.q01.BlockData

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem rawError36_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 36 j))=rawError 36 := by decide +kernel
theorem rawError37_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 37 j))=rawError 37 := by decide +kernel
theorem rawError38_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 38 j))=rawError 38 := by decide +kernel
theorem rawError39_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 39 j))=rawError 39 := by decide +kernel
end ThomsonNegative.Certificate.Correction.q01
