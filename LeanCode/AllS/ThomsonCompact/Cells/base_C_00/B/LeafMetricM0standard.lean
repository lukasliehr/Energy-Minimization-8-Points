import ThomsonCompact.Cells.base_C_00.B.Metric
/-! F3f leaf MetricM0standard of the two-piece cell base_C_00 (generated). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_base_C_00.B.Leaves
open ThomsonCompact.Floor ThomsonCompact.Cells.C_base_C_00.B

theorem metricM0standard : checkTheta ThomsonCompact.Cells.C_base_C_00_PL.B.nbM0standard ThomsonCompact.Cells.C_base_C_00_PL.B.wzM0standard 64 mbM0standard ThomsonCompact.Cells.C_base_C_00_PL.B.zrowsM0standard exM0standard klM0standard thM0standard = true ∧
    checkTotal ((List.range 1).map fun _ => Nat.max ThomsonCompact.Cells.C_base_C_00_PL.B.GcM0standard ThomsonCompact.Cells.C_base_C_00_PR.B.GcM0standard) (Nat.max ThomsonCompact.Cells.C_base_C_00_PL.B.GetaM0standard ThomsonCompact.Cells.C_base_C_00_PR.B.GetaM0standard)
      (Nat.max ThomsonCompact.Cells.C_base_C_00_PL.B.GcM0standard ThomsonCompact.Cells.C_base_C_00_PR.B.GcM0standard + Nat.max ThomsonCompact.Cells.C_base_C_00_PL.B.GetaM0standard ThomsonCompact.Cells.C_base_C_00_PR.B.GetaM0standard) thM0standard (32 + mbM0standard) 1 = true := ⟨by decide +kernel, by decide +kernel⟩

end ThomsonCompact.Cells.C_base_C_00.B.Leaves
