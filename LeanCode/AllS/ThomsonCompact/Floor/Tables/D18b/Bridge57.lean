import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle131
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle132
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle133
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle134
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle135
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle136
/-! Bridge of the re-expanded rows 131-136 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge131 : rowBridgeOk 272 1083 12 10 51 1 row131 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h131 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge132 : rowBridgeOk 272 1083 12 10 51 1 row132 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h132 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge133 : rowBridgeOk 272 1083 12 10 51 1 row133 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h133 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge134 : rowBridgeOk 272 1083 12 10 51 1 row134 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h134 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge135 : rowBridgeOk 272 1083 12 10 51 1 row135 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h135 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge136 : rowBridgeOk 272 1083 12 10 51 1 row136 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h136 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
