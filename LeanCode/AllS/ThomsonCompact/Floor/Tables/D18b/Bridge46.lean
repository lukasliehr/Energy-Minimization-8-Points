import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle065
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle066
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle067
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle068
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle069
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle070
/-! Bridge of the re-expanded rows 65-70 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge065 : rowBridgeOk 272 1083 12 10 222 1 row065 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h065 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge066 : rowBridgeOk 272 1083 12 10 300 1 row066 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h066 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge067 : rowBridgeOk 272 1083 12 10 404 1 row067 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h067 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge068 : rowBridgeOk 272 1083 12 10 222 1 row068 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h068 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge069 : rowBridgeOk 272 1083 12 10 236 1 row069 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h069 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge070 : rowBridgeOk 272 1083 12 10 315 1 row070 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h070 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
