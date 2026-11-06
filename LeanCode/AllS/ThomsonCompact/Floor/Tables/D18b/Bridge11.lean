import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows2
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle011
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle012
/-! Bridge of the re-expanded rows 11-12 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge011 : rowBridgeOk 272 1083 12 10 412 1 row011 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h011 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge012 : rowBridgeOk 272 1083 12 10 375 1 row012 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h012 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
