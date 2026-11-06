import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle101
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle102
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle103
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle104
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle105
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle106
/-! Bridge of the re-expanded rows 101-106 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge101 : rowBridgeOk 272 1083 12 10 210 1 row101 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h101 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge102 : rowBridgeOk 272 1083 12 10 196 1 row102 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h102 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge103 : rowBridgeOk 272 1083 12 10 51 1 row103 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h103 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge104 : rowBridgeOk 272 1083 12 10 207 1 row104 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h104 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge105 : rowBridgeOk 272 1083 12 10 207 1 row105 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h105 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge106 : rowBridgeOk 272 1083 12 10 196 1 row106 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h106 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
