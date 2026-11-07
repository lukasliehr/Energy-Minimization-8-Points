import ThomsonCompact.Floor.Tables.D18b.Table
/-! D18 corrected blocks: coordinates within the block orders (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem uvF0 : ∀ i, i < 11 → (row (0 + i)).u < 9 ∧ (row (0 + i)).v < 9 := by decide +kernel

theorem uvF1 : ∀ i, i < 4 → (row (11 + i)).u < 8 ∧ (row (11 + i)).v < 8 := by decide +kernel

theorem uvM0plus : ∀ i, i < 250 → (row (15 + i)).u < 48 ∧ (row (15 + i)).v < 48 := by decide +kernel

theorem uvM0standard : ∀ i, i < 7 → (row (265 + i)).u < 65 ∧ (row (265 + i)).v < 65 := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
