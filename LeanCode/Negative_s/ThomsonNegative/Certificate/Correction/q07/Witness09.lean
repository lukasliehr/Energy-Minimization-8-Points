import ThomsonNegative.Certificate.Correction.q07.WitnessData
import ThomsonNegative.Certificate.Correction.RowSound
import ThomsonNegative.Certificate.Correction.q07.Contract36
import ThomsonNegative.Certificate.Correction.q07.Contract37
import ThomsonNegative.Certificate.Correction.q07.Contract38
import ThomsonNegative.Certificate.Correction.q07.Contract39

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem witness36_certified : RowCertified argument residual witness36 := by
  refine ⟨norm36_positive, inverse36_checked, columns36_checked, centers36_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction36_0
  · exact contraction36_1
  · exact contraction36_2
  · exact contraction36_3
  · exact contraction36_4
  · exact contraction36_5
  · exact contraction36_6
  · exact contraction36_7
  · exact contraction36_8
  · exact contraction36_9
  · exact contraction36_10
theorem witness37_certified : RowCertified argument residual witness37 := by
  refine ⟨norm37_positive, inverse37_checked, columns37_checked, centers37_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction37_0
  · exact contraction37_1
  · exact contraction37_2
  · exact contraction37_3
  · exact contraction37_4
  · exact contraction37_5
  · exact contraction37_6
  · exact contraction37_7
  · exact contraction37_8
  · exact contraction37_9
  · exact contraction37_10
theorem witness38_certified : RowCertified argument residual witness38 := by
  refine ⟨norm38_positive, inverse38_checked, columns38_checked, centers38_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction38_0
  · exact contraction38_1
  · exact contraction38_2
  · exact contraction38_3
  · exact contraction38_4
  · exact contraction38_5
  · exact contraction38_6
  · exact contraction38_7
  · exact contraction38_8
  · exact contraction38_9
  · exact contraction38_10
theorem witness39_certified : RowCertified argument residual witness39 := by
  refine ⟨norm39_positive, inverse39_checked, columns39_checked, centers39_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction39_0
  · exact contraction39_1
  · exact contraction39_2
  · exact contraction39_3
  · exact contraction39_4
  · exact contraction39_5
  · exact contraction39_6
  · exact contraction39_7
  · exact contraction39_8
  · exact contraction39_9
  · exact contraction39_10
end ThomsonNegative.Certificate.Correction.q07
