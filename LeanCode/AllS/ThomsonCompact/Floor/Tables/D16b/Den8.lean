import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.B.FixedDec
import ThomsonCompact.Fixed.D16.GTable
import ThomsonCompact.Floor.Tables.D16b.Rows10
/-! Denominator bridge of the re-expanded rows 200-201 (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D16b
open ThomsonCompact.Floor.B

theorem den200 : denOk 68 8 8 3 row200 (FD.lamG ThomsonCompact.Fixed.D16.gtab 200) (FD.dqG ThomsonCompact.Fixed.D16.gtab 200) (FD.dzC ThomsonCompact.Fixed.D16.gtab 200) = true := by decide +kernel

theorem den201 : denOk 68 8 8 3 row201 (FD.lamG ThomsonCompact.Fixed.D16.gtab 201) (FD.dqG ThomsonCompact.Fixed.D16.gtab 201) (FD.dzC ThomsonCompact.Fixed.D16.gtab 201) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D16b
