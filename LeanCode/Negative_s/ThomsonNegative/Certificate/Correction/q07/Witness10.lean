import ThomsonNegative.Certificate.Correction.q07.WitnessData
import ThomsonNegative.Certificate.Correction.RowSound
import ThomsonNegative.Certificate.Correction.q07.Contract40
import ThomsonNegative.Certificate.Correction.q07.Contract41
import ThomsonNegative.Certificate.Correction.q07.Contract42
import ThomsonNegative.Certificate.Correction.q07.Contract43

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem witness40_certified : RowCertified argument residual witness40 := by
  refine ⟨norm40_positive, inverse40_checked, columns40_checked, centers40_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction40_0
  · exact contraction40_1
  · exact contraction40_2
  · exact contraction40_3
  · exact contraction40_4
  · exact contraction40_5
  · exact contraction40_6
  · exact contraction40_7
  · exact contraction40_8
  · exact contraction40_9
  · exact contraction40_10
theorem witness41_certified : RowCertified argument residual witness41 := by
  refine ⟨norm41_positive, inverse41_checked, columns41_checked, centers41_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction41_0
  · exact contraction41_1
  · exact contraction41_2
  · exact contraction41_3
  · exact contraction41_4
  · exact contraction41_5
  · exact contraction41_6
  · exact contraction41_7
  · exact contraction41_8
  · exact contraction41_9
  · exact contraction41_10
theorem witness42_certified : RowCertified argument residual witness42 := by
  refine ⟨norm42_positive, inverse42_checked, columns42_checked, centers42_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction42_0
  · exact contraction42_1
  · exact contraction42_2
  · exact contraction42_3
  · exact contraction42_4
  · exact contraction42_5
  · exact contraction42_6
  · exact contraction42_7
  · exact contraction42_8
  · exact contraction42_9
  · exact contraction42_10
theorem witness43_certified : RowCertified argument residual witness43 := by
  refine ⟨norm43_positive, inverse43_checked, columns43_checked, centers43_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction43_0
  · exact contraction43_1
  · exact contraction43_2
  · exact contraction43_3
  · exact contraction43_4
  · exact contraction43_5
  · exact contraction43_6
  · exact contraction43_7
  · exact contraction43_8
  · exact contraction43_9
  · exact contraction43_10
end ThomsonNegative.Certificate.Correction.q07
