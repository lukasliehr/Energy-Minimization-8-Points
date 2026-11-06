import ThomsonCompact.CoeffMap.ECheck.Def

/-! One-time check of the sparse coefficient table of block 12. -/

namespace ThomsonCompact.CoeffMap.D12

theorem checkE_12 : checkE 12 = true := by decide +kernel

end ThomsonCompact.CoeffMap.D12
