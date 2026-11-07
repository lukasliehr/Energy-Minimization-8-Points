import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle113
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle114
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle115
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle116
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle117
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle118
/-! Bridge of the re-expanded rows 113-118 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge113 : rowBridgeOk 272 1083 12 10 196 1 row113 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h113 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge114 : rowBridgeOk 272 1083 12 10 196 1 row114 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h114 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge115 : rowBridgeOk 272 1083 12 10 208 1 row115 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h115 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge116 : rowBridgeOk 272 1083 12 10 196 1 row116 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h116 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge117 : rowBridgeOk 272 1083 12 10 197 1 row117 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h117 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge118 : rowBridgeOk 272 1083 12 10 51 1 row118 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h118 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
