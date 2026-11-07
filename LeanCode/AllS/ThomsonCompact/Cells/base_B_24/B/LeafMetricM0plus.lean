import ThomsonCompact.Cells.base_B_24.B.Metric
/-! F3c leaf MetricM0plus of cell base_B_24 (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Cells.C_base_B_24.B.Leaves
open ThomsonCompact.Floor ThomsonCompact.Cells.C_base_B_24.B

theorem metricM0plus : checkTheta nbM0plus wzM0plus 64 mbM0plus zrowsM0plus exM0plus klM0plus thM0plus = true ∧
    checkTotal ((List.range 1).map fun _ => GcM0plus) GetaM0plus (GcM0plus + GetaM0plus) thM0plus (32 + mbM0plus) 4 = true := ⟨by decide +kernel, by decide +kernel⟩

end ThomsonCompact.Cells.C_base_B_24.B.Leaves
