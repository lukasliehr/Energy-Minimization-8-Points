import ThomsonNegative.Certificate.Correction.q01.WitnessData
import ThomsonNegative.Certificate.Correction.RowSound
import ThomsonNegative.Certificate.Correction.q01.Contract32
import ThomsonNegative.Certificate.Correction.q01.Contract33
import ThomsonNegative.Certificate.Correction.q01.Contract34
import ThomsonNegative.Certificate.Correction.q01.Contract35

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem witness32_certified : RowCertified argument residual witness32 := by
  refine ⟨norm32_positive, inverse32_checked, columns32_checked, centers32_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction32_0
  · exact contraction32_1
  · exact contraction32_2
  · exact contraction32_3
  · exact contraction32_4
  · exact contraction32_5
  · exact contraction32_6
  · exact contraction32_7
  · exact contraction32_8
  · exact contraction32_9
  · exact contraction32_10
theorem witness33_certified : RowCertified argument residual witness33 := by
  refine ⟨norm33_positive, inverse33_checked, columns33_checked, centers33_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction33_0
  · exact contraction33_1
  · exact contraction33_2
  · exact contraction33_3
  · exact contraction33_4
  · exact contraction33_5
  · exact contraction33_6
  · exact contraction33_7
  · exact contraction33_8
  · exact contraction33_9
  · exact contraction33_10
theorem witness34_certified : RowCertified argument residual witness34 := by
  refine ⟨norm34_positive, inverse34_checked, columns34_checked, centers34_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction34_0
  · exact contraction34_1
  · exact contraction34_2
  · exact contraction34_3
  · exact contraction34_4
  · exact contraction34_5
  · exact contraction34_6
  · exact contraction34_7
  · exact contraction34_8
  · exact contraction34_9
  · exact contraction34_10
theorem witness35_certified : RowCertified argument residual witness35 := by
  refine ⟨norm35_positive, inverse35_checked, columns35_checked, centers35_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction35_0
  · exact contraction35_1
  · exact contraction35_2
  · exact contraction35_3
  · exact contraction35_4
  · exact contraction35_5
  · exact contraction35_6
  · exact contraction35_7
  · exact contraction35_8
  · exact contraction35_9
  · exact contraction35_10
end ThomsonNegative.Certificate.Correction.q01
