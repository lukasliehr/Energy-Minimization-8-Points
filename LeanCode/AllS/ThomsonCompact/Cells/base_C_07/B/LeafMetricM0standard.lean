import ThomsonCompact.Cells.base_C_07.B.Metric
/-! F3c leaf MetricM0standard of cell base_C_07 (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Cells.C_base_C_07.B.Leaves
open ThomsonCompact.Floor ThomsonCompact.Cells.C_base_C_07.B

theorem metricM0standard : checkTheta nbM0standard wzM0standard 64 mbM0standard zrowsM0standard exM0standard klM0standard thM0standard = true ∧
    checkTotal ((List.range 1).map fun _ => GcM0standard) GetaM0standard (GcM0standard + GetaM0standard) thM0standard (32 + mbM0standard) 4 = true := ⟨by decide +kernel, by decide +kernel⟩

end ThomsonCompact.Cells.C_base_C_07.B.Leaves
