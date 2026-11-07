import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows7
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle034
/-! Bridge of the re-expanded rows 34-34 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge034 : rowBridgeOk 272 1083 12 10 821 1 row034 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h034 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
