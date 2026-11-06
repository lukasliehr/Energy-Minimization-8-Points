import ThomsonCompact.CoeffMap.ECheck.Def

/-! One-time check of the sparse coefficient table of block 10. -/

namespace ThomsonCompact.CoeffMap.D12

theorem checkE_10 : checkE 10 = true := by decide +kernel

end ThomsonCompact.CoeffMap.D12
