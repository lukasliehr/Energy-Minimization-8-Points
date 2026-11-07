import ThomsonNegative.Certificate.Correction.q01.BlockData

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem rawError32_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 32 j))=rawError 32 := by decide +kernel
theorem rawError33_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 33 j))=rawError 33 := by decide +kernel
theorem rawError34_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 34 j))=rawError 34 := by decide +kernel
theorem rawError35_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 35 j))=rawError 35 := by decide +kernel
end ThomsonNegative.Certificate.Correction.q01
