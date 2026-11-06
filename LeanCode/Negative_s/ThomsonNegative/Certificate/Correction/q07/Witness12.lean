import ThomsonNegative.Certificate.Correction.q07.WitnessData
import ThomsonNegative.Certificate.Correction.RowSound
import ThomsonNegative.Certificate.Correction.q07.Contract48
import ThomsonNegative.Certificate.Correction.q07.Contract49
import ThomsonNegative.Certificate.Correction.q07.Contract50
import ThomsonNegative.Certificate.Correction.q07.Contract51

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem witness48_certified : RowCertified argument residual witness48 := by
  refine ⟨norm48_positive, inverse48_checked, columns48_checked, centers48_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction48_0
  · exact contraction48_1
  · exact contraction48_2
  · exact contraction48_3
  · exact contraction48_4
  · exact contraction48_5
  · exact contraction48_6
  · exact contraction48_7
  · exact contraction48_8
  · exact contraction48_9
  · exact contraction48_10
theorem witness49_certified : RowCertified argument residual witness49 := by
  refine ⟨norm49_positive, inverse49_checked, columns49_checked, centers49_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction49_0
  · exact contraction49_1
  · exact contraction49_2
  · exact contraction49_3
  · exact contraction49_4
  · exact contraction49_5
  · exact contraction49_6
  · exact contraction49_7
  · exact contraction49_8
  · exact contraction49_9
  · exact contraction49_10
theorem witness50_certified : RowCertified argument residual witness50 := by
  refine ⟨norm50_positive, inverse50_checked, columns50_checked, centers50_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction50_0
  · exact contraction50_1
  · exact contraction50_2
  · exact contraction50_3
  · exact contraction50_4
  · exact contraction50_5
  · exact contraction50_6
  · exact contraction50_7
  · exact contraction50_8
  · exact contraction50_9
  · exact contraction50_10
theorem witness51_certified : RowCertified argument residual witness51 := by
  refine ⟨norm51_positive, inverse51_checked, columns51_checked, centers51_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction51_0
  · exact contraction51_1
  · exact contraction51_2
  · exact contraction51_3
  · exact contraction51_4
  · exact contraction51_5
  · exact contraction51_6
  · exact contraction51_7
  · exact contraction51_8
  · exact contraction51_9
  · exact contraction51_10
end ThomsonNegative.Certificate.Correction.q07
