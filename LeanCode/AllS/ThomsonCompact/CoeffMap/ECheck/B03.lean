import ThomsonCompact.CoeffMap.ECheck.Def

/-! One-time check of the sparse coefficient table of block 3. -/

namespace ThomsonCompact.CoeffMap.D12

theorem checkE_3 : checkE 3 = true := by decide +kernel

end ThomsonCompact.CoeffMap.D12
