import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D12b.Rows4
import AllS.Units.N_AI.N_fixed_tables.D12.HRows040
/-! Bridge of the re-expanded rows 40-49 to the old `FixedTables.D12` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D12b
open ThomsonCompact.Floor.B

theorem bridge040 : rowBridgeOk 100 19 6 4 259 1 row040 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h040 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge041 : rowBridgeOk 100 19 6 4 3 1 row041 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h041 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge042 : rowBridgeOk 100 19 6 4 3 1 row042 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h042 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge043 : rowBridgeOk 100 19 6 4 316 1 row043 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h043 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge044 : rowBridgeOk 100 19 6 4 74 1 row044 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h044 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge045 : rowBridgeOk 100 19 6 4 4 1 row045 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h045 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge046 : rowBridgeOk 100 19 6 4 349 1 row046 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h046 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge047 : rowBridgeOk 100 19 6 4 3 1 row047 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h047 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge048 : rowBridgeOk 100 19 6 4 3 1 row048 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h048 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge049 : rowBridgeOk 100 19 6 4 4 1 row049 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h049 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D12b
