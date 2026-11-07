import ThomsonNegative.Certificate.Correction.q09.WitnessData
import ThomsonNegative.Certificate.Correction.RowSound
import ThomsonNegative.Certificate.Correction.q09.Contract52
import ThomsonNegative.Certificate.Correction.q09.Contract53
import ThomsonNegative.Certificate.Correction.q09.Contract54
import ThomsonNegative.Certificate.Correction.q09.Contract55

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem witness52_certified : RowCertified argument residual witness52 := by
  refine ⟨norm52_positive, inverse52_checked, columns52_checked, centers52_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction52_0
  · exact contraction52_1
  · exact contraction52_2
  · exact contraction52_3
  · exact contraction52_4
  · exact contraction52_5
  · exact contraction52_6
  · exact contraction52_7
  · exact contraction52_8
  · exact contraction52_9
  · exact contraction52_10
theorem witness53_certified : RowCertified argument residual witness53 := by
  refine ⟨norm53_positive, inverse53_checked, columns53_checked, centers53_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction53_0
  · exact contraction53_1
  · exact contraction53_2
  · exact contraction53_3
  · exact contraction53_4
  · exact contraction53_5
  · exact contraction53_6
  · exact contraction53_7
  · exact contraction53_8
  · exact contraction53_9
  · exact contraction53_10
theorem witness54_certified : RowCertified argument residual witness54 := by
  refine ⟨norm54_positive, inverse54_checked, columns54_checked, centers54_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction54_0
  · exact contraction54_1
  · exact contraction54_2
  · exact contraction54_3
  · exact contraction54_4
  · exact contraction54_5
  · exact contraction54_6
  · exact contraction54_7
  · exact contraction54_8
  · exact contraction54_9
  · exact contraction54_10
theorem witness55_certified : RowCertified argument residual witness55 := by
  refine ⟨norm55_positive, inverse55_checked, columns55_checked, centers55_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction55_0
  · exact contraction55_1
  · exact contraction55_2
  · exact contraction55_3
  · exact contraction55_4
  · exact contraction55_5
  · exact contraction55_6
  · exact contraction55_7
  · exact contraction55_8
  · exact contraction55_9
  · exact contraction55_10
end ThomsonNegative.Certificate.Correction.q09
