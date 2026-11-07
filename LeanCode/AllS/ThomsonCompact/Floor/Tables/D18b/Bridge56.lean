import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle125
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle126
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle127
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle128
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle129
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle130
/-! Bridge of the re-expanded rows 125-130 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge125 : rowBridgeOk 272 1083 12 10 51 1 row125 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h125 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge126 : rowBridgeOk 272 1083 12 10 51 1 row126 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h126 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge127 : rowBridgeOk 272 1083 12 10 51 1 row127 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h127 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge128 : rowBridgeOk 272 1083 12 10 51 1 row128 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h128 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge129 : rowBridgeOk 272 1083 12 10 51 1 row129 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h129 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge130 : rowBridgeOk 272 1083 12 10 51 1 row130 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h130 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
