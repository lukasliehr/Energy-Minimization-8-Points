import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle191
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle192
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle193
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle194
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle195
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle196
/-! Bridge of the re-expanded rows 191-196 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge191 : rowBridgeOk 272 1083 12 10 51 1 row191 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h191 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge192 : rowBridgeOk 272 1083 12 10 51 1 row192 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h192 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge193 : rowBridgeOk 272 1083 12 10 51 1 row193 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h193 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge194 : rowBridgeOk 272 1083 12 10 51 1 row194 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h194 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge195 : rowBridgeOk 272 1083 12 10 51 1 row195 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h195 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge196 : rowBridgeOk 272 1083 12 10 51 1 row196 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h196 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
