import ThomsonNegative.Certificate.Correction.q01.WitnessData
import ThomsonNegative.Certificate.Correction.RowSound
import ThomsonNegative.Certificate.Correction.q01.Contract12
import ThomsonNegative.Certificate.Correction.q01.Contract13
import ThomsonNegative.Certificate.Correction.q01.Contract14
import ThomsonNegative.Certificate.Correction.q01.Contract15

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem witness12_certified : RowCertified argument residual witness12 := by
  refine ⟨norm12_positive, inverse12_checked, columns12_checked, centers12_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction12_0
  · exact contraction12_1
  · exact contraction12_2
  · exact contraction12_3
  · exact contraction12_4
  · exact contraction12_5
  · exact contraction12_6
  · exact contraction12_7
  · exact contraction12_8
  · exact contraction12_9
  · exact contraction12_10
theorem witness13_certified : RowCertified argument residual witness13 := by
  refine ⟨norm13_positive, inverse13_checked, columns13_checked, centers13_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction13_0
  · exact contraction13_1
  · exact contraction13_2
  · exact contraction13_3
  · exact contraction13_4
  · exact contraction13_5
  · exact contraction13_6
  · exact contraction13_7
  · exact contraction13_8
  · exact contraction13_9
  · exact contraction13_10
theorem witness14_certified : RowCertified argument residual witness14 := by
  refine ⟨norm14_positive, inverse14_checked, columns14_checked, centers14_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction14_0
  · exact contraction14_1
  · exact contraction14_2
  · exact contraction14_3
  · exact contraction14_4
  · exact contraction14_5
  · exact contraction14_6
  · exact contraction14_7
  · exact contraction14_8
  · exact contraction14_9
  · exact contraction14_10
theorem witness15_certified : RowCertified argument residual witness15 := by
  refine ⟨norm15_positive, inverse15_checked, columns15_checked, centers15_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction15_0
  · exact contraction15_1
  · exact contraction15_2
  · exact contraction15_3
  · exact contraction15_4
  · exact contraction15_5
  · exact contraction15_6
  · exact contraction15_7
  · exact contraction15_8
  · exact contraction15_9
  · exact contraction15_10
end ThomsonNegative.Certificate.Correction.q01
