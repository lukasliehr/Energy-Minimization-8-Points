import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D12b.Rows6
import AllS.Units.N_AI.N_fixed_tables.D12.HRows060
/-! Bridge of the re-expanded rows 60-69 to the old `FixedTables.D12` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D12b
open ThomsonCompact.Floor.B

theorem bridge060 : rowBridgeOk 100 19 6 4 3 1 row060 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h060 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge061 : rowBridgeOk 100 19 6 4 3 1 row061 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h061 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge062 : rowBridgeOk 100 19 6 4 3 1 row062 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h062 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge063 : rowBridgeOk 100 19 6 4 67 1 row063 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h063 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge064 : rowBridgeOk 100 19 6 4 62 1 row064 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h064 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge065 : rowBridgeOk 100 19 6 4 3 1 row065 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h065 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge066 : rowBridgeOk 100 19 6 4 3 1 row066 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h066 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge067 : rowBridgeOk 100 19 6 4 62 1 row067 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h067 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge068 : rowBridgeOk 100 19 6 4 3 1 row068 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h068 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge069 : rowBridgeOk 100 19 6 4 3 1 row069 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h069 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D12b
