import ThomsonNegative.Certificate.Correction.q01.WitnessData
import ThomsonNegative.Certificate.Correction.RowSound
import ThomsonNegative.Certificate.Correction.q01.Contract60
import ThomsonNegative.Certificate.Correction.q01.Contract61
import ThomsonNegative.Certificate.Correction.q01.Contract62
import ThomsonNegative.Certificate.Correction.q01.Contract63

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem witness60_certified : RowCertified argument residual witness60 := by
  refine ⟨norm60_positive, inverse60_checked, columns60_checked, centers60_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction60_0
  · exact contraction60_1
  · exact contraction60_2
  · exact contraction60_3
  · exact contraction60_4
  · exact contraction60_5
  · exact contraction60_6
  · exact contraction60_7
  · exact contraction60_8
  · exact contraction60_9
  · exact contraction60_10
theorem witness61_certified : RowCertified argument residual witness61 := by
  refine ⟨norm61_positive, inverse61_checked, columns61_checked, centers61_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction61_0
  · exact contraction61_1
  · exact contraction61_2
  · exact contraction61_3
  · exact contraction61_4
  · exact contraction61_5
  · exact contraction61_6
  · exact contraction61_7
  · exact contraction61_8
  · exact contraction61_9
  · exact contraction61_10
theorem witness62_certified : RowCertified argument residual witness62 := by
  refine ⟨norm62_positive, inverse62_checked, columns62_checked, centers62_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction62_0
  · exact contraction62_1
  · exact contraction62_2
  · exact contraction62_3
  · exact contraction62_4
  · exact contraction62_5
  · exact contraction62_6
  · exact contraction62_7
  · exact contraction62_8
  · exact contraction62_9
  · exact contraction62_10
theorem witness63_certified : RowCertified argument residual witness63 := by
  refine ⟨norm63_positive, inverse63_checked, columns63_checked, centers63_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction63_0
  · exact contraction63_1
  · exact contraction63_2
  · exact contraction63_3
  · exact contraction63_4
  · exact contraction63_5
  · exact contraction63_6
  · exact contraction63_7
  · exact contraction63_8
  · exact contraction63_9
  · exact contraction63_10
end ThomsonNegative.Certificate.Correction.q01
