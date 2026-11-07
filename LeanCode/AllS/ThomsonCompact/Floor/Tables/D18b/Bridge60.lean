import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle149
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle150
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle151
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle152
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle153
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle154
/-! Bridge of the re-expanded rows 149-154 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge149 : rowBridgeOk 272 1083 12 10 51 1 row149 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h149 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge150 : rowBridgeOk 272 1083 12 10 51 1 row150 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h150 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge151 : rowBridgeOk 272 1083 12 10 51 1 row151 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h151 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge152 : rowBridgeOk 272 1083 12 10 51 1 row152 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h152 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge153 : rowBridgeOk 272 1083 12 10 51 1 row153 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h153 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge154 : rowBridgeOk 272 1083 12 10 51 1 row154 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h154 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
