import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D12b.Rows0
import AllS.Units.N_AI.N_fixed_tables.D12.HRows000
/-! Bridge of the re-expanded rows 0-9 to the old `FixedTables.D12` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D12b
open ThomsonCompact.Floor.B

theorem bridge000 : rowBridgeOk 100 19 6 4 297 1 row000 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h000 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge001 : rowBridgeOk 100 19 6 4 290 1 row001 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h001 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge002 : rowBridgeOk 100 19 6 4 285 1 row002 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h002 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge003 : rowBridgeOk 100 19 6 4 278 1 row003 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h003 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge004 : rowBridgeOk 100 19 6 4 271 1 row004 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h004 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge005 : rowBridgeOk 100 19 6 4 264 1 row005 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h005 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge006 : rowBridgeOk 100 19 6 4 285 1 row006 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h006 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge007 : rowBridgeOk 100 19 6 4 279 1 row007 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h007 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge008 : rowBridgeOk 100 19 6 4 273 1 row008 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h008 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge009 : rowBridgeOk 100 19 6 4 264 1 row009 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h009 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D12b
