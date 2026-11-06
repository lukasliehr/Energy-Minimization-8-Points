import ThomsonCompact.Cells.base_A_08.B.Metric
/-! F3c leaf MetricF0 of cell base_A_08 (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Cells.C_base_A_08.B.Leaves
open ThomsonCompact.Floor ThomsonCompact.Cells.C_base_A_08.B

theorem metricF0 : checkTheta nbF0 wzF0 64 mbF0 zrowsF0 exF0 klF0 thF0 = true ∧
    checkTotal ((List.range 1).map fun _ => GcF0) GetaF0 (GcF0 + GetaF0) thF0 (32 + mbF0) 4 = true := ⟨by decide +kernel, by decide +kernel⟩

end ThomsonCompact.Cells.C_base_A_08.B.Leaves
