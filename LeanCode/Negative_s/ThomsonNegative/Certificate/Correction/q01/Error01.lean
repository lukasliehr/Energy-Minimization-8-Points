import ThomsonNegative.Certificate.Correction.q01.BlockData

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem rawError4_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 4 j))=rawError 4 := by decide +kernel
theorem rawError5_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 5 j))=rawError 5 := by decide +kernel
theorem rawError6_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 6 j))=rawError 6 := by decide +kernel
theorem rawError7_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 7 j))=rawError 7 := by decide +kernel
end ThomsonNegative.Certificate.Correction.q01
