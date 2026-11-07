import ThomsonNegative.Certificate.Correction.q09.WitnessData
import ThomsonNegative.Certificate.Correction.RowSound
import ThomsonNegative.Certificate.Correction.q09.Contract64
import ThomsonNegative.Certificate.Correction.q09.Contract65
import ThomsonNegative.Certificate.Correction.q09.Contract66
import ThomsonNegative.Certificate.Correction.q09.Contract67

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem witness64_certified : RowCertified argument residual witness64 := by
  refine ⟨norm64_positive, inverse64_checked, columns64_checked, centers64_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction64_0
  · exact contraction64_1
  · exact contraction64_2
  · exact contraction64_3
  · exact contraction64_4
  · exact contraction64_5
  · exact contraction64_6
  · exact contraction64_7
  · exact contraction64_8
  · exact contraction64_9
  · exact contraction64_10
theorem witness65_certified : RowCertified argument residual witness65 := by
  refine ⟨norm65_positive, inverse65_checked, columns65_checked, centers65_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction65_0
  · exact contraction65_1
  · exact contraction65_2
  · exact contraction65_3
  · exact contraction65_4
  · exact contraction65_5
  · exact contraction65_6
  · exact contraction65_7
  · exact contraction65_8
  · exact contraction65_9
  · exact contraction65_10
theorem witness66_certified : RowCertified argument residual witness66 := by
  refine ⟨norm66_positive, inverse66_checked, columns66_checked, centers66_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction66_0
  · exact contraction66_1
  · exact contraction66_2
  · exact contraction66_3
  · exact contraction66_4
  · exact contraction66_5
  · exact contraction66_6
  · exact contraction66_7
  · exact contraction66_8
  · exact contraction66_9
  · exact contraction66_10
theorem witness67_certified : RowCertified argument residual witness67 := by
  refine ⟨norm67_positive, inverse67_checked, columns67_checked, centers67_checked, ?_⟩
  intro k
  fin_cases k
  · exact contraction67_0
  · exact contraction67_1
  · exact contraction67_2
  · exact contraction67_3
  · exact contraction67_4
  · exact contraction67_5
  · exact contraction67_6
  · exact contraction67_7
  · exact contraction67_8
  · exact contraction67_9
  · exact contraction67_10
end ThomsonNegative.Certificate.Correction.q09
