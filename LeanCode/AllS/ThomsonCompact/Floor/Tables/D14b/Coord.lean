import ThomsonCompact.Floor.Tables.D14b.Table
import ThomsonCompact.Fixed.D14.LTable
/-! Output coordinates of the re-expanded D14 rows (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D14b
open ThomsonCompact.Floor.B

theorem coords : ∀ j, j < 145 → Nat.land (Nat.shiftRight (ThomsonCompact.Fixed.D14.ltab.oinfo j) 8) 255 = (row j).u ∧
    Nat.land (Nat.shiftRight (ThomsonCompact.Fixed.D14.ltab.oinfo j) 16) 255 = (row j).v := by decide +kernel

end ThomsonCompact.Floor.Tables.D14b
