import ThomsonNegative.Certificate.Correction.q01.WitnessData
import ThomsonNegative.Certificate.Correction.RowSound
import ThomsonNegative.Certificate.Correction.q01.Contract20
import ThomsonNegative.Certificate.Correction.q01.Contract21
import ThomsonNegative.Certificate.Correction.q01.Contract22
import ThomsonNegative.Certificate.Correction.q01.Contract23

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem witness20_certified : RowCertified argument residual witness20 := by
  refine ⟨norm20_positive, inverse20_checked, columns20_checked, centers20_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction20_0
  · exact contraction20_1
  · exact contraction20_2
  · exact contraction20_3
  · exact contraction20_4
  · exact contraction20_5
  · exact contraction20_6
  · exact contraction20_7
  · exact contraction20_8
  · exact contraction20_9
  · exact contraction20_10
theorem witness21_certified : RowCertified argument residual witness21 := by
  refine ⟨norm21_positive, inverse21_checked, columns21_checked, centers21_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction21_0
  · exact contraction21_1
  · exact contraction21_2
  · exact contraction21_3
  · exact contraction21_4
  · exact contraction21_5
  · exact contraction21_6
  · exact contraction21_7
  · exact contraction21_8
  · exact contraction21_9
  · exact contraction21_10
theorem witness22_certified : RowCertified argument residual witness22 := by
  refine ⟨norm22_positive, inverse22_checked, columns22_checked, centers22_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction22_0
  · exact contraction22_1
  · exact contraction22_2
  · exact contraction22_3
  · exact contraction22_4
  · exact contraction22_5
  · exact contraction22_6
  · exact contraction22_7
  · exact contraction22_8
  · exact contraction22_9
  · exact contraction22_10
theorem witness23_certified : RowCertified argument residual witness23 := by
  refine ⟨norm23_positive, inverse23_checked, columns23_checked, centers23_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction23_0
  · exact contraction23_1
  · exact contraction23_2
  · exact contraction23_3
  · exact contraction23_4
  · exact contraction23_5
  · exact contraction23_6
  · exact contraction23_7
  · exact contraction23_8
  · exact contraction23_9
  · exact contraction23_10
end ThomsonNegative.Certificate.Correction.q01
