import ThomsonNegative.Certificate.Correction.q07.WitnessData
import ThomsonNegative.Certificate.Correction.RowSound
import ThomsonNegative.Certificate.Correction.q07.Contract56
import ThomsonNegative.Certificate.Correction.q07.Contract57
import ThomsonNegative.Certificate.Correction.q07.Contract58
import ThomsonNegative.Certificate.Correction.q07.Contract59

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem witness56_certified : RowCertified argument residual witness56 := by
  refine ⟨norm56_positive, inverse56_checked, columns56_checked, centers56_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction56_0
  · exact contraction56_1
  · exact contraction56_2
  · exact contraction56_3
  · exact contraction56_4
  · exact contraction56_5
  · exact contraction56_6
  · exact contraction56_7
  · exact contraction56_8
  · exact contraction56_9
  · exact contraction56_10
theorem witness57_certified : RowCertified argument residual witness57 := by
  refine ⟨norm57_positive, inverse57_checked, columns57_checked, centers57_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction57_0
  · exact contraction57_1
  · exact contraction57_2
  · exact contraction57_3
  · exact contraction57_4
  · exact contraction57_5
  · exact contraction57_6
  · exact contraction57_7
  · exact contraction57_8
  · exact contraction57_9
  · exact contraction57_10
theorem witness58_certified : RowCertified argument residual witness58 := by
  refine ⟨norm58_positive, inverse58_checked, columns58_checked, centers58_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction58_0
  · exact contraction58_1
  · exact contraction58_2
  · exact contraction58_3
  · exact contraction58_4
  · exact contraction58_5
  · exact contraction58_6
  · exact contraction58_7
  · exact contraction58_8
  · exact contraction58_9
  · exact contraction58_10
theorem witness59_certified : RowCertified argument residual witness59 := by
  refine ⟨norm59_positive, inverse59_checked, columns59_checked, centers59_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction59_0
  · exact contraction59_1
  · exact contraction59_2
  · exact contraction59_3
  · exact contraction59_4
  · exact contraction59_5
  · exact contraction59_6
  · exact contraction59_7
  · exact contraction59_8
  · exact contraction59_9
  · exact contraction59_10
end ThomsonNegative.Certificate.Correction.q07
