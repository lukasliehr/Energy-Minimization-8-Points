import ThomsonNegative.Certificate.Correction.q07.WitnessData
import ThomsonNegative.Certificate.Correction.RowSound
import ThomsonNegative.Certificate.Correction.q07.Contract28
import ThomsonNegative.Certificate.Correction.q07.Contract29
import ThomsonNegative.Certificate.Correction.q07.Contract30
import ThomsonNegative.Certificate.Correction.q07.Contract31

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem witness28_certified : RowCertified argument residual witness28 := by
  refine ⟨norm28_positive, inverse28_checked, columns28_checked, centers28_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction28_0
  · exact contraction28_1
  · exact contraction28_2
  · exact contraction28_3
  · exact contraction28_4
  · exact contraction28_5
  · exact contraction28_6
  · exact contraction28_7
  · exact contraction28_8
  · exact contraction28_9
  · exact contraction28_10
theorem witness29_certified : RowCertified argument residual witness29 := by
  refine ⟨norm29_positive, inverse29_checked, columns29_checked, centers29_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction29_0
  · exact contraction29_1
  · exact contraction29_2
  · exact contraction29_3
  · exact contraction29_4
  · exact contraction29_5
  · exact contraction29_6
  · exact contraction29_7
  · exact contraction29_8
  · exact contraction29_9
  · exact contraction29_10
theorem witness30_certified : RowCertified argument residual witness30 := by
  refine ⟨norm30_positive, inverse30_checked, columns30_checked, centers30_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction30_0
  · exact contraction30_1
  · exact contraction30_2
  · exact contraction30_3
  · exact contraction30_4
  · exact contraction30_5
  · exact contraction30_6
  · exact contraction30_7
  · exact contraction30_8
  · exact contraction30_9
  · exact contraction30_10
theorem witness31_certified : RowCertified argument residual witness31 := by
  refine ⟨norm31_positive, inverse31_checked, columns31_checked, centers31_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction31_0
  · exact contraction31_1
  · exact contraction31_2
  · exact contraction31_3
  · exact contraction31_4
  · exact contraction31_5
  · exact contraction31_6
  · exact contraction31_7
  · exact contraction31_8
  · exact contraction31_9
  · exact contraction31_10
end ThomsonNegative.Certificate.Correction.q07
