import ThomsonCompact.Floor.Tables.D14b.Table
/-! D14 corrected blocks: coordinates within the block orders (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D14b
open ThomsonCompact.Floor.B

theorem uvF0 : ∀ i, i < 11 → (row (0 + i)).u < 7 ∧ (row (0 + i)).v < 7 := by decide +kernel

theorem uvF1 : ∀ i, i < 4 → (row (11 + i)).u < 6 ∧ (row (11 + i)).v < 6 := by decide +kernel

theorem uvM0plus : ∀ i, i < 122 → (row (15 + i)).u < 26 ∧ (row (15 + i)).v < 26 := by decide +kernel

theorem uvM0standard : ∀ i, i < 8 → (row (137 + i)).u < 32 ∧ (row (137 + i)).v < 32 := by decide +kernel

end ThomsonCompact.Floor.Tables.D14b
