import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle263
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle264
/-! Bridge of the re-expanded rows 263-264 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge263 : rowBridgeOk 272 1083 12 10 51 1 row263 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h263 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge264 : rowBridgeOk 272 1083 12 10 51 1 row264 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h264 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
