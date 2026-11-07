import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D12b.Rows5
import AllS.Units.N_AI.N_fixed_tables.D12.HRows050
/-! Bridge of the re-expanded rows 50-59 to the old `FixedTables.D12` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D12b
open ThomsonCompact.Floor.B

theorem bridge050 : rowBridgeOk 100 19 6 4 3 1 row050 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h050 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge051 : rowBridgeOk 100 19 6 4 62 1 row051 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h051 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge052 : rowBridgeOk 100 19 6 4 3 1 row052 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h052 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge053 : rowBridgeOk 100 19 6 4 3 1 row053 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h053 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge054 : rowBridgeOk 100 19 6 4 3 1 row054 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h054 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge055 : rowBridgeOk 100 19 6 4 3 1 row055 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h055 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge056 : rowBridgeOk 100 19 6 4 3 1 row056 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h056 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge057 : rowBridgeOk 100 19 6 4 4 1 row057 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h057 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge058 : rowBridgeOk 100 19 6 4 61 1 row058 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h058 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge059 : rowBridgeOk 100 19 6 4 62 1 row059 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h059 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D12b
