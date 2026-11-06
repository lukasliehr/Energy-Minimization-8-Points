import ThomsonCompact.CoeffMap.ECheck.Def

/-! One-time check of the sparse coefficient table of block 5. -/

namespace ThomsonCompact.CoeffMap.D12

theorem checkE_5 : checkE 5 = true := by decide +kernel

end ThomsonCompact.CoeffMap.D12
