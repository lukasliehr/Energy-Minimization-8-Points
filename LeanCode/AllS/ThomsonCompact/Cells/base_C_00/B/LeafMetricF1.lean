import ThomsonCompact.Cells.base_C_00.B.Metric
/-! F3f leaf MetricF1 of the two-piece cell base_C_00 (generated). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_base_C_00.B.Leaves
open ThomsonCompact.Floor ThomsonCompact.Cells.C_base_C_00.B

theorem metricF1 : checkTheta ThomsonCompact.Cells.C_base_C_00_PL.B.nbF1 ThomsonCompact.Cells.C_base_C_00_PL.B.wzF1 64 mbF1 ThomsonCompact.Cells.C_base_C_00_PL.B.zrowsF1 exF1 klF1 thF1 = true ∧
    checkTotal ((List.range 1).map fun _ => Nat.max ThomsonCompact.Cells.C_base_C_00_PL.B.GcF1 ThomsonCompact.Cells.C_base_C_00_PR.B.GcF1) (Nat.max ThomsonCompact.Cells.C_base_C_00_PL.B.GetaF1 ThomsonCompact.Cells.C_base_C_00_PR.B.GetaF1)
      (Nat.max ThomsonCompact.Cells.C_base_C_00_PL.B.GcF1 ThomsonCompact.Cells.C_base_C_00_PR.B.GcF1 + Nat.max ThomsonCompact.Cells.C_base_C_00_PL.B.GetaF1 ThomsonCompact.Cells.C_base_C_00_PR.B.GetaF1) thF1 (32 + mbF1) 1 = true := ⟨by decide +kernel, by decide +kernel⟩

end ThomsonCompact.Cells.C_base_C_00.B.Leaves
