import ThomsonNegative.Certificate.Correction.q07.BlockData

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem rawError52_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 52 j))=rawError 52 := by decide +kernel
theorem rawError53_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 53 j))=rawError 53 := by decide +kernel
theorem rawError54_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 54 j))=rawError 54 := by decide +kernel
theorem rawError55_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 55 j))=rawError 55 := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
