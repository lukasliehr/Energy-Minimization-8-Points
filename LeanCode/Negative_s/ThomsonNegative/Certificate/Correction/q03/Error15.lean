import ThomsonNegative.Certificate.Correction.q03.BlockData

namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Certificate
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem rawError60_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 60 j))=rawError 60 := by decide +kernel
theorem rawError61_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 61 j))=rawError 61 := by decide +kernel
theorem rawError62_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 62 j))=rawError 62 := by decide +kernel
theorem rawError63_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 63 j))=rawError 63 := by decide +kernel
end ThomsonNegative.Certificate.Correction.q03
