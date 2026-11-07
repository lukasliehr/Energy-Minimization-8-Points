import ThomsonNegative.Certificate.Correction.q07.WitnessData
import ThomsonNegative.Certificate.Correction.RowSound
import ThomsonNegative.Certificate.Correction.q07.Contract00
import ThomsonNegative.Certificate.Correction.q07.Contract01
import ThomsonNegative.Certificate.Correction.q07.Contract02
import ThomsonNegative.Certificate.Correction.q07.Contract03

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem witness0_certified : RowCertified argument residual witness0 := by
  refine ⟨norm0_positive, inverse0_checked, columns0_checked, centers0_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction0_0
  · exact contraction0_1
  · exact contraction0_2
  · exact contraction0_3
  · exact contraction0_4
  · exact contraction0_5
  · exact contraction0_6
  · exact contraction0_7
  · exact contraction0_8
  · exact contraction0_9
  · exact contraction0_10
theorem witness1_certified : RowCertified argument residual witness1 := by
  refine ⟨norm1_positive, inverse1_checked, columns1_checked, centers1_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction1_0
  · exact contraction1_1
  · exact contraction1_2
  · exact contraction1_3
  · exact contraction1_4
  · exact contraction1_5
  · exact contraction1_6
  · exact contraction1_7
  · exact contraction1_8
  · exact contraction1_9
  · exact contraction1_10
theorem witness2_certified : RowCertified argument residual witness2 := by
  refine ⟨norm2_positive, inverse2_checked, columns2_checked, centers2_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction2_0
  · exact contraction2_1
  · exact contraction2_2
  · exact contraction2_3
  · exact contraction2_4
  · exact contraction2_5
  · exact contraction2_6
  · exact contraction2_7
  · exact contraction2_8
  · exact contraction2_9
  · exact contraction2_10
theorem witness3_certified : RowCertified argument residual witness3 := by
  refine ⟨norm3_positive, inverse3_checked, columns3_checked, centers3_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction3_0
  · exact contraction3_1
  · exact contraction3_2
  · exact contraction3_3
  · exact contraction3_4
  · exact contraction3_5
  · exact contraction3_6
  · exact contraction3_7
  · exact contraction3_8
  · exact contraction3_9
  · exact contraction3_10
end ThomsonNegative.Certificate.Correction.q07
