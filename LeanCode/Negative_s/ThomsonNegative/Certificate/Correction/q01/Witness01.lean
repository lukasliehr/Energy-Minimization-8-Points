import ThomsonNegative.Certificate.Correction.q01.WitnessData
import ThomsonNegative.Certificate.Correction.RowSound
import ThomsonNegative.Certificate.Correction.q01.Contract04
import ThomsonNegative.Certificate.Correction.q01.Contract05
import ThomsonNegative.Certificate.Correction.q01.Contract06
import ThomsonNegative.Certificate.Correction.q01.Contract07

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem witness4_certified : RowCertified argument residual witness4 := by
  refine ⟨norm4_positive, inverse4_checked, columns4_checked, centers4_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction4_0
  · exact contraction4_1
  · exact contraction4_2
  · exact contraction4_3
  · exact contraction4_4
  · exact contraction4_5
  · exact contraction4_6
  · exact contraction4_7
  · exact contraction4_8
  · exact contraction4_9
  · exact contraction4_10
theorem witness5_certified : RowCertified argument residual witness5 := by
  refine ⟨norm5_positive, inverse5_checked, columns5_checked, centers5_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction5_0
  · exact contraction5_1
  · exact contraction5_2
  · exact contraction5_3
  · exact contraction5_4
  · exact contraction5_5
  · exact contraction5_6
  · exact contraction5_7
  · exact contraction5_8
  · exact contraction5_9
  · exact contraction5_10
theorem witness6_certified : RowCertified argument residual witness6 := by
  refine ⟨norm6_positive, inverse6_checked, columns6_checked, centers6_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction6_0
  · exact contraction6_1
  · exact contraction6_2
  · exact contraction6_3
  · exact contraction6_4
  · exact contraction6_5
  · exact contraction6_6
  · exact contraction6_7
  · exact contraction6_8
  · exact contraction6_9
  · exact contraction6_10
theorem witness7_certified : RowCertified argument residual witness7 := by
  refine ⟨norm7_positive, inverse7_checked, columns7_checked, centers7_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction7_0
  · exact contraction7_1
  · exact contraction7_2
  · exact contraction7_3
  · exact contraction7_4
  · exact contraction7_5
  · exact contraction7_6
  · exact contraction7_7
  · exact contraction7_8
  · exact contraction7_9
  · exact contraction7_10
end ThomsonNegative.Certificate.Correction.q01
