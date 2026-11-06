import ThomsonCompact.CoeffMap.ECheck.Def

/-! One-time check of the sparse coefficient table of block 4. -/

namespace ThomsonCompact.CoeffMap.D12

theorem checkE_4 : checkE 4 = true := by decide +kernel

end ThomsonCompact.CoeffMap.D12
