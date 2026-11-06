import ThomsonCompact.CoeffMap.ECheck.Def

/-! One-time check of the sparse coefficient table of block 8. -/

namespace ThomsonCompact.CoeffMap.D12

theorem checkE_8 : checkE 8 = true := by decide +kernel

end ThomsonCompact.CoeffMap.D12
