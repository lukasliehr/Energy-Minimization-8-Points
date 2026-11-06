import ThomsonCompact.Cells.base_C_00.B.Metric
/-! F3f leaf MetricF0 of the two-piece cell base_C_00 (generated). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_base_C_00.B.Leaves
open ThomsonCompact.Floor ThomsonCompact.Cells.C_base_C_00.B

theorem metricF0 : checkTheta ThomsonCompact.Cells.C_base_C_00_PL.B.nbF0 ThomsonCompact.Cells.C_base_C_00_PL.B.wzF0 64 mbF0 ThomsonCompact.Cells.C_base_C_00_PL.B.zrowsF0 exF0 klF0 thF0 = true ∧
    checkTotal ((List.range 1).map fun _ => Nat.max ThomsonCompact.Cells.C_base_C_00_PL.B.GcF0 ThomsonCompact.Cells.C_base_C_00_PR.B.GcF0) (Nat.max ThomsonCompact.Cells.C_base_C_00_PL.B.GetaF0 ThomsonCompact.Cells.C_base_C_00_PR.B.GetaF0)
      (Nat.max ThomsonCompact.Cells.C_base_C_00_PL.B.GcF0 ThomsonCompact.Cells.C_base_C_00_PR.B.GcF0 + Nat.max ThomsonCompact.Cells.C_base_C_00_PL.B.GetaF0 ThomsonCompact.Cells.C_base_C_00_PR.B.GetaF0) thF0 (32 + mbF0) 1 = true := ⟨by decide +kernel, by decide +kernel⟩

end ThomsonCompact.Cells.C_base_C_00.B.Leaves
