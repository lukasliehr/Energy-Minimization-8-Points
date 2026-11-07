import ThomsonNegative.Certificate.Correction.q03.WitnessData
import ThomsonNegative.Certificate.Correction.RowSound
import ThomsonNegative.Certificate.Correction.q03.Contract44
import ThomsonNegative.Certificate.Correction.q03.Contract45
import ThomsonNegative.Certificate.Correction.q03.Contract46
import ThomsonNegative.Certificate.Correction.q03.Contract47

namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem witness44_certified : RowCertified argument residual witness44 := by
  refine ⟨norm44_positive, inverse44_checked, columns44_checked, centers44_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction44_0
  · exact contraction44_1
  · exact contraction44_2
  · exact contraction44_3
  · exact contraction44_4
  · exact contraction44_5
  · exact contraction44_6
  · exact contraction44_7
  · exact contraction44_8
  · exact contraction44_9
  · exact contraction44_10
theorem witness45_certified : RowCertified argument residual witness45 := by
  refine ⟨norm45_positive, inverse45_checked, columns45_checked, centers45_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction45_0
  · exact contraction45_1
  · exact contraction45_2
  · exact contraction45_3
  · exact contraction45_4
  · exact contraction45_5
  · exact contraction45_6
  · exact contraction45_7
  · exact contraction45_8
  · exact contraction45_9
  · exact contraction45_10
theorem witness46_certified : RowCertified argument residual witness46 := by
  refine ⟨norm46_positive, inverse46_checked, columns46_checked, centers46_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction46_0
  · exact contraction46_1
  · exact contraction46_2
  · exact contraction46_3
  · exact contraction46_4
  · exact contraction46_5
  · exact contraction46_6
  · exact contraction46_7
  · exact contraction46_8
  · exact contraction46_9
  · exact contraction46_10
theorem witness47_certified : RowCertified argument residual witness47 := by
  refine ⟨norm47_positive, inverse47_checked, columns47_checked, centers47_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction47_0
  · exact contraction47_1
  · exact contraction47_2
  · exact contraction47_3
  · exact contraction47_4
  · exact contraction47_5
  · exact contraction47_6
  · exact contraction47_7
  · exact contraction47_8
  · exact contraction47_9
  · exact contraction47_10
end ThomsonNegative.Certificate.Correction.q03
