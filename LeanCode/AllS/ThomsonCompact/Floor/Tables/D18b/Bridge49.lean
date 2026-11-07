import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle083
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle084
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle085
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle086
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle087
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle088
/-! Bridge of the re-expanded rows 83-88 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge083 : rowBridgeOk 272 1083 12 10 51 1 row083 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h083 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge084 : rowBridgeOk 272 1083 12 10 51 1 row084 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h084 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge085 : rowBridgeOk 272 1083 12 10 51 1 row085 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h085 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge086 : rowBridgeOk 272 1083 12 10 51 1 row086 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h086 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge087 : rowBridgeOk 272 1083 12 10 196 1 row087 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h087 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge088 : rowBridgeOk 272 1083 12 10 195 1 row088 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h088 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
