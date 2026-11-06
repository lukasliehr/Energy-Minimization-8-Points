import ThomsonNegative.Certificate.Correction.q05.WitnessData
import ThomsonNegative.Certificate.Correction.RowSound
import ThomsonNegative.Certificate.Correction.q05.Contract08
import ThomsonNegative.Certificate.Correction.q05.Contract09
import ThomsonNegative.Certificate.Correction.q05.Contract10
import ThomsonNegative.Certificate.Correction.q05.Contract11

namespace ThomsonNegative.Certificate.Correction.q05
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem witness8_certified : RowCertified argument residual witness8 := by
  refine ⟨norm8_positive, inverse8_checked, columns8_checked, centers8_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction8_0
  · exact contraction8_1
  · exact contraction8_2
  · exact contraction8_3
  · exact contraction8_4
  · exact contraction8_5
  · exact contraction8_6
  · exact contraction8_7
  · exact contraction8_8
  · exact contraction8_9
  · exact contraction8_10
theorem witness9_certified : RowCertified argument residual witness9 := by
  refine ⟨norm9_positive, inverse9_checked, columns9_checked, centers9_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction9_0
  · exact contraction9_1
  · exact contraction9_2
  · exact contraction9_3
  · exact contraction9_4
  · exact contraction9_5
  · exact contraction9_6
  · exact contraction9_7
  · exact contraction9_8
  · exact contraction9_9
  · exact contraction9_10
theorem witness10_certified : RowCertified argument residual witness10 := by
  refine ⟨norm10_positive, inverse10_checked, columns10_checked, centers10_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction10_0
  · exact contraction10_1
  · exact contraction10_2
  · exact contraction10_3
  · exact contraction10_4
  · exact contraction10_5
  · exact contraction10_6
  · exact contraction10_7
  · exact contraction10_8
  · exact contraction10_9
  · exact contraction10_10
theorem witness11_certified : RowCertified argument residual witness11 := by
  refine ⟨norm11_positive, inverse11_checked, columns11_checked, centers11_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction11_0
  · exact contraction11_1
  · exact contraction11_2
  · exact contraction11_3
  · exact contraction11_4
  · exact contraction11_5
  · exact contraction11_6
  · exact contraction11_7
  · exact contraction11_8
  · exact contraction11_9
  · exact contraction11_10
end ThomsonNegative.Certificate.Correction.q05
