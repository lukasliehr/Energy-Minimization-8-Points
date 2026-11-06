import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle185
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle186
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle187
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle188
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle189
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle190
/-! Bridge of the re-expanded rows 185-190 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge185 : rowBridgeOk 272 1083 12 10 51 1 row185 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h185 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge186 : rowBridgeOk 272 1083 12 10 51 1 row186 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h186 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge187 : rowBridgeOk 272 1083 12 10 51 1 row187 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h187 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge188 : rowBridgeOk 272 1083 12 10 51 1 row188 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h188 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge189 : rowBridgeOk 272 1083 12 10 51 1 row189 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h189 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge190 : rowBridgeOk 272 1083 12 10 51 1 row190 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h190 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
