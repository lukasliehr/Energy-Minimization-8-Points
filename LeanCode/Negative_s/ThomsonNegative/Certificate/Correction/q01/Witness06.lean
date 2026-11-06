import ThomsonNegative.Certificate.Correction.q01.WitnessData
import ThomsonNegative.Certificate.Correction.RowSound
import ThomsonNegative.Certificate.Correction.q01.Contract24
import ThomsonNegative.Certificate.Correction.q01.Contract25
import ThomsonNegative.Certificate.Correction.q01.Contract26
import ThomsonNegative.Certificate.Correction.q01.Contract27

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem witness24_certified : RowCertified argument residual witness24 := by
  refine ⟨norm24_positive, inverse24_checked, columns24_checked, centers24_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction24_0
  · exact contraction24_1
  · exact contraction24_2
  · exact contraction24_3
  · exact contraction24_4
  · exact contraction24_5
  · exact contraction24_6
  · exact contraction24_7
  · exact contraction24_8
  · exact contraction24_9
  · exact contraction24_10
theorem witness25_certified : RowCertified argument residual witness25 := by
  refine ⟨norm25_positive, inverse25_checked, columns25_checked, centers25_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction25_0
  · exact contraction25_1
  · exact contraction25_2
  · exact contraction25_3
  · exact contraction25_4
  · exact contraction25_5
  · exact contraction25_6
  · exact contraction25_7
  · exact contraction25_8
  · exact contraction25_9
  · exact contraction25_10
theorem witness26_certified : RowCertified argument residual witness26 := by
  refine ⟨norm26_positive, inverse26_checked, columns26_checked, centers26_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction26_0
  · exact contraction26_1
  · exact contraction26_2
  · exact contraction26_3
  · exact contraction26_4
  · exact contraction26_5
  · exact contraction26_6
  · exact contraction26_7
  · exact contraction26_8
  · exact contraction26_9
  · exact contraction26_10
theorem witness27_certified : RowCertified argument residual witness27 := by
  refine ⟨norm27_positive, inverse27_checked, columns27_checked, centers27_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction27_0
  · exact contraction27_1
  · exact contraction27_2
  · exact contraction27_3
  · exact contraction27_4
  · exact contraction27_5
  · exact contraction27_6
  · exact contraction27_7
  · exact contraction27_8
  · exact contraction27_9
  · exact contraction27_10
end ThomsonNegative.Certificate.Correction.q01
