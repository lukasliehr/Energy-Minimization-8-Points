import ThomsonCompact.CoeffMap.ECheck.Def

/-! One-time check of the sparse coefficient table of block 2. -/

namespace ThomsonCompact.CoeffMap.D12

theorem checkE_2 : checkE 2 = true := by decide +kernel

end ThomsonCompact.CoeffMap.D12
