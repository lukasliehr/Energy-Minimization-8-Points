import ThomsonNegative.Certificate.Correction.q07.WitnessData
import ThomsonNegative.Certificate.Correction.RowSound
import ThomsonNegative.Certificate.Correction.q07.Contract16
import ThomsonNegative.Certificate.Correction.q07.Contract17
import ThomsonNegative.Certificate.Correction.q07.Contract18
import ThomsonNegative.Certificate.Correction.q07.Contract19

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem witness16_certified : RowCertified argument residual witness16 := by
  refine ⟨norm16_positive, inverse16_checked, columns16_checked, centers16_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction16_0
  · exact contraction16_1
  · exact contraction16_2
  · exact contraction16_3
  · exact contraction16_4
  · exact contraction16_5
  · exact contraction16_6
  · exact contraction16_7
  · exact contraction16_8
  · exact contraction16_9
  · exact contraction16_10
theorem witness17_certified : RowCertified argument residual witness17 := by
  refine ⟨norm17_positive, inverse17_checked, columns17_checked, centers17_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction17_0
  · exact contraction17_1
  · exact contraction17_2
  · exact contraction17_3
  · exact contraction17_4
  · exact contraction17_5
  · exact contraction17_6
  · exact contraction17_7
  · exact contraction17_8
  · exact contraction17_9
  · exact contraction17_10
theorem witness18_certified : RowCertified argument residual witness18 := by
  refine ⟨norm18_positive, inverse18_checked, columns18_checked, centers18_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction18_0
  · exact contraction18_1
  · exact contraction18_2
  · exact contraction18_3
  · exact contraction18_4
  · exact contraction18_5
  · exact contraction18_6
  · exact contraction18_7
  · exact contraction18_8
  · exact contraction18_9
  · exact contraction18_10
theorem witness19_certified : RowCertified argument residual witness19 := by
  refine ⟨norm19_positive, inverse19_checked, columns19_checked, centers19_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction19_0
  · exact contraction19_1
  · exact contraction19_2
  · exact contraction19_3
  · exact contraction19_4
  · exact contraction19_5
  · exact contraction19_6
  · exact contraction19_7
  · exact contraction19_8
  · exact contraction19_9
  · exact contraction19_10
end ThomsonNegative.Certificate.Correction.q07
