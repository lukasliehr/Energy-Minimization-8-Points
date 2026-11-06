import ThomsonCompact.Floor.Tables.D16b.Table
/-! D16 corrected blocks: coordinates within the block orders (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D16b
open ThomsonCompact.Floor.B

theorem uvF0 : ∀ i, i < 11 → (row (0 + i)).u < 8 ∧ (row (0 + i)).v < 8 := by decide +kernel

theorem uvF1 : ∀ i, i < 4 → (row (11 + i)).u < 7 ∧ (row (11 + i)).v < 7 := by decide +kernel

theorem uvM0plus : ∀ i, i < 179 → (row (15 + i)).u < 36 ∧ (row (15 + i)).v < 36 := by decide +kernel

theorem uvM0standard : ∀ i, i < 8 → (row (194 + i)).u < 47 ∧ (row (194 + i)).v < 47 := by decide +kernel

end ThomsonCompact.Floor.Tables.D16b
