import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle197
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle198
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle199
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle200
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle201
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle202
/-! Bridge of the re-expanded rows 197-202 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge197 : rowBridgeOk 272 1083 12 10 51 1 row197 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h197 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge198 : rowBridgeOk 272 1083 12 10 51 1 row198 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h198 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge199 : rowBridgeOk 272 1083 12 10 51 1 row199 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h199 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge200 : rowBridgeOk 272 1083 12 10 51 1 row200 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h200 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge201 : rowBridgeOk 272 1083 12 10 51 1 row201 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h201 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge202 : rowBridgeOk 272 1083 12 10 51 1 row202 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h202 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
