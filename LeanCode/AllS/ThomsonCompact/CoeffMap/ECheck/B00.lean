import ThomsonCompact.CoeffMap.ECheck.Def

/-! One-time check of the sparse coefficient table of block 0. -/

namespace ThomsonCompact.CoeffMap.D12

theorem checkE_0 : checkE 0 = true := by decide +kernel

end ThomsonCompact.CoeffMap.D12
