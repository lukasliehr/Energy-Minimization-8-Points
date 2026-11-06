import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle161
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle162
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle163
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle164
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle165
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle166
/-! Bridge of the re-expanded rows 161-166 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge161 : rowBridgeOk 272 1083 12 10 51 1 row161 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h161 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge162 : rowBridgeOk 272 1083 12 10 51 1 row162 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h162 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge163 : rowBridgeOk 272 1083 12 10 51 1 row163 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h163 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge164 : rowBridgeOk 272 1083 12 10 51 1 row164 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h164 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge165 : rowBridgeOk 272 1083 12 10 51 1 row165 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h165 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge166 : rowBridgeOk 272 1083 12 10 51 1 row166 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h166 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
