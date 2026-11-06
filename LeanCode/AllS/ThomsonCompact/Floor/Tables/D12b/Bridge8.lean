import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D12b.Rows8
import AllS.Units.N_AI.N_fixed_tables.D12.HRows080
/-! Bridge of the re-expanded rows 80-89 to the old `FixedTables.D12` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D12b
open ThomsonCompact.Floor.B

theorem bridge080 : rowBridgeOk 100 19 6 4 3 1 row080 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h080 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge081 : rowBridgeOk 100 19 6 4 3 1 row081 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h081 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge082 : rowBridgeOk 100 19 6 4 3 1 row082 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h082 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge083 : rowBridgeOk 100 19 6 4 3 1 row083 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h083 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge084 : rowBridgeOk 100 19 6 4 3 1 row084 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h084 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge085 : rowBridgeOk 100 19 6 4 3 1 row085 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h085 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge086 : rowBridgeOk 100 19 6 4 3 1 row086 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h086 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge087 : rowBridgeOk 100 19 6 4 3 1 row087 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h087 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge088 : rowBridgeOk 100 19 6 4 3 1 row088 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h088 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge089 : rowBridgeOk 100 19 6 4 3 1 row089 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h089 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D12b
