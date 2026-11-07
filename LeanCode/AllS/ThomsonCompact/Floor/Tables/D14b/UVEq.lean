import ThomsonCompact.Floor.Tables.D14b.UV
import ThomsonCompact.Floor.Tables.D14b.Table
/-! One-time checks: the packed block coordinates are those of the table rows (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Floor.Tables.D14b
open ThomsonCompact.Floor.B

theorem uvsF0_eq : uvsF0 = uvsOf row 0 11 := by decide +kernel

theorem uvsF1_eq : uvsF1 = uvsOf row 11 4 := by decide +kernel

theorem uvsM0plus_eq : uvsM0plus = uvsOf row 15 122 := by decide +kernel

theorem uvsM0standard_eq : uvsM0standard = uvsOf row 137 8 := by decide +kernel

end ThomsonCompact.Floor.Tables.D14b
