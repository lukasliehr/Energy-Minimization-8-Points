import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle137
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle138
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle139
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle140
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle141
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle142
/-! Bridge of the re-expanded rows 137-142 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge137 : rowBridgeOk 272 1083 12 10 51 1 row137 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h137 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge138 : rowBridgeOk 272 1083 12 10 51 1 row138 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h138 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge139 : rowBridgeOk 272 1083 12 10 51 1 row139 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h139 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge140 : rowBridgeOk 272 1083 12 10 51 1 row140 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h140 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge141 : rowBridgeOk 272 1083 12 10 51 1 row141 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h141 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge142 : rowBridgeOk 272 1083 12 10 51 1 row142 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h142 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
