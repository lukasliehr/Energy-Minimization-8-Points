import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle143
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle144
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle145
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle146
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle147
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle148
/-! Bridge of the re-expanded rows 143-148 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge143 : rowBridgeOk 272 1083 12 10 51 1 row143 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h143 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge144 : rowBridgeOk 272 1083 12 10 51 1 row144 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h144 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge145 : rowBridgeOk 272 1083 12 10 51 1 row145 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h145 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge146 : rowBridgeOk 272 1083 12 10 51 1 row146 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h146 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge147 : rowBridgeOk 272 1083 12 10 51 1 row147 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h147 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge148 : rowBridgeOk 272 1083 12 10 51 1 row148 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h148 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
