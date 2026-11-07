import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle155
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle156
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle157
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle158
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle159
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle160
/-! Bridge of the re-expanded rows 155-160 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge155 : rowBridgeOk 272 1083 12 10 51 1 row155 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h155 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge156 : rowBridgeOk 272 1083 12 10 51 1 row156 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h156 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge157 : rowBridgeOk 272 1083 12 10 51 1 row157 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h157 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge158 : rowBridgeOk 272 1083 12 10 51 1 row158 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h158 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge159 : rowBridgeOk 272 1083 12 10 51 1 row159 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h159 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge160 : rowBridgeOk 272 1083 12 10 51 1 row160 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h160 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
