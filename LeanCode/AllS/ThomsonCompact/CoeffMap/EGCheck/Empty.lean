import ThomsonCompact.CoeffMap.BSum

/-! One-time check (F2d): the coefficient lists of the empty pair groups `g ≥ ngD12 bi` are empty (so their pieces are
`zeroTM` and their real functions vanish; `CoeffMap.BSumSound.empty_piece`, `empty_gpk`). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.CoeffMap

theorem emptyGroupsOk_d12 : emptyGroupsOk = true := by decide +kernel

end ThomsonCompact.CoeffMap
