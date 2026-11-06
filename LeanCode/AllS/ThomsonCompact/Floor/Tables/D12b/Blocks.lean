import ThomsonCompact.Floor.Tables.D12b.Table
/-! D12 corrected blocks: row ranges and coordinates within the block order (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D12b
open ThomsonCompact.Floor.B

theorem uvF0 : ∀ i, i < 11 → (row (0 + i)).u < 6 ∧ (row (0 + i)).v < 6 := by decide +kernel

theorem uvF1 : ∀ i, i < 4 → (row (11 + i)).u < 5 ∧ (row (11 + i)).v < 5 := by decide +kernel

theorem uvM0plus : ∀ i, i < 79 → (row (15 + i)).u < 18 ∧ (row (15 + i)).v < 18 := by decide +kernel

theorem uvM0standard : ∀ i, i < 6 → (row (94 + i)).u < 20 ∧ (row (94 + i)).v < 20 := by decide +kernel

end ThomsonCompact.Floor.Tables.D12b
