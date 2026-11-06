import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows9
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle053
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle054
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle055
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle056
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle057
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle058
/-! Bridge of the re-expanded rows 53-58 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge053 : rowBridgeOk 272 1083 12 10 181 1 row053 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h053 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge054 : rowBridgeOk 272 1083 12 10 222 1 row054 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h054 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge055 : rowBridgeOk 272 1083 12 10 311 1 row055 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h055 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge056 : rowBridgeOk 272 1083 12 10 222 1 row056 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h056 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge057 : rowBridgeOk 272 1083 12 10 235 1 row057 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h057 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge058 : rowBridgeOk 272 1083 12 10 326 1 row058 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h058 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
