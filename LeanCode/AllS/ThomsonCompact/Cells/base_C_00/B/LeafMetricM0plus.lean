import ThomsonCompact.Cells.base_C_00.B.Metric
/-! F3f leaf MetricM0plus of the two-piece cell base_C_00 (generated). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_base_C_00.B.Leaves
open ThomsonCompact.Floor ThomsonCompact.Cells.C_base_C_00.B

theorem metricM0plus : checkTheta ThomsonCompact.Cells.C_base_C_00_PL.B.nbM0plus ThomsonCompact.Cells.C_base_C_00_PL.B.wzM0plus 64 mbM0plus ThomsonCompact.Cells.C_base_C_00_PL.B.zrowsM0plus exM0plus klM0plus thM0plus = true ∧
    checkTotal ((List.range 1).map fun _ => Nat.max ThomsonCompact.Cells.C_base_C_00_PL.B.GcM0plus ThomsonCompact.Cells.C_base_C_00_PR.B.GcM0plus) (Nat.max ThomsonCompact.Cells.C_base_C_00_PL.B.GetaM0plus ThomsonCompact.Cells.C_base_C_00_PR.B.GetaM0plus)
      (Nat.max ThomsonCompact.Cells.C_base_C_00_PL.B.GcM0plus ThomsonCompact.Cells.C_base_C_00_PR.B.GcM0plus + Nat.max ThomsonCompact.Cells.C_base_C_00_PL.B.GetaM0plus ThomsonCompact.Cells.C_base_C_00_PR.B.GetaM0plus) thM0plus (32 + mbM0plus) 1 = true := ⟨by decide +kernel, by decide +kernel⟩

end ThomsonCompact.Cells.C_base_C_00.B.Leaves
