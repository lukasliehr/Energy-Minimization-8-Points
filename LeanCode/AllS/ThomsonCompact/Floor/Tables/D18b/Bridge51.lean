import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle095
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle096
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle097
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle098
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle099
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle100
/-! Bridge of the re-expanded rows 95-100 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge095 : rowBridgeOk 272 1083 12 10 195 1 row095 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h095 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge096 : rowBridgeOk 272 1083 12 10 221 1 row096 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h096 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge097 : rowBridgeOk 272 1083 12 10 207 1 row097 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h097 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge098 : rowBridgeOk 272 1083 12 10 51 1 row098 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h098 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge099 : rowBridgeOk 272 1083 12 10 51 1 row099 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h099 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge100 : rowBridgeOk 272 1083 12 10 179 1 row100 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h100 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
