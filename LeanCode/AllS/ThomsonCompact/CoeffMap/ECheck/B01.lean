import ThomsonCompact.CoeffMap.ECheck.Def

/-! One-time check of the sparse coefficient table of block 1. -/

namespace ThomsonCompact.CoeffMap.D12

theorem checkE_1 : checkE 1 = true := by decide +kernel

end ThomsonCompact.CoeffMap.D12
