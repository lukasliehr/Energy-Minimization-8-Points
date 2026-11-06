import ThomsonCompact.Cells.base_B_26.B.Metric
/-! F3c leaf MetricF1 of cell base_B_26 (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Cells.C_base_B_26.B.Leaves
open ThomsonCompact.Floor ThomsonCompact.Cells.C_base_B_26.B

theorem metricF1 : checkTheta nbF1 wzF1 64 mbF1 zrowsF1 exF1 klF1 thF1 = true ∧
    checkTotal ((List.range 1).map fun _ => GcF1) GetaF1 (GcF1 + GetaF1) thF1 (32 + mbF1) 4 = true := ⟨by decide +kernel, by decide +kernel⟩

end ThomsonCompact.Cells.C_base_B_26.B.Leaves
