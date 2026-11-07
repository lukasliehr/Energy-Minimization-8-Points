import ThomsonNegative.Certificate.Correction.q07.BlockData

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem rawError44_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 44 j))=rawError 44 := by decide +kernel
theorem rawError45_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 45 j))=rawError 45 := by decide +kernel
theorem rawError46_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 46 j))=rawError 46 := by decide +kernel
theorem rawError47_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 47 j))=rawError 47 := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
