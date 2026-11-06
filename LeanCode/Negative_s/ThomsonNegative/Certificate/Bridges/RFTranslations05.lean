import ThomsonNegative.Certificate.Bridges.RFChecks05
import ThomsonNegative.Certificate.BasisData
import ThomsonNegative.Certificate.Bridges.BasisSource
import ThomsonNegative.Certificate.Bridges.RFPolynomial
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure.Packed
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
theorem rf50_translation (a : ℝ) :
    (BasisData.rf50).eval (a-83/256)=(SourceBasis.rf50).eval a := by
  apply translated_rf_of_scaled (BasisData.rf50) (SourceBasis.rf50) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e50n.sound RFChecks.e50n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e50n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e50n.left 0)=integerCoefficients (BasisData.rf50).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e50n.target0=affineShift (SourceBasis.rf50).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf50).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1011550697553920:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf50).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(3951369912320:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1011550697553920:ℤ)] (a-(83/256:ℝ))=(1011550697553920:ℝ) by simp [evalZ,horner]),(show evalZ [(3951369912320:ℤ)] (a-(83/256:ℝ))=(3951369912320:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf50] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf50).numerator.denominator = 3951369912320 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf50).numerator) (a-(83/256:ℝ)) /
      (3951369912320:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf50).numerator a
    simp only [SourceBasis.rf50]
    nlinarith [hh]
  · have hh := RFChecks.e50d.sound RFChecks.e50d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e50d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e50d.left 0)=factorCoefficients (BasisData.rf50).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e50d.target0=affineShift (SourceBasis.rf50).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf50).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf50).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ))=(2251799813685248:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf50] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf50).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf50).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf50).denominator a
    simp only [SourceBasis.rf50]
    nlinarith [hh]
  · norm_num [BasisData.rf50,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf51_translation (a : ℝ) :
    (BasisData.rf51).eval (a-83/256)=(SourceBasis.rf51).eval a := by
  apply translated_rf_of_scaled (BasisData.rf51) (SourceBasis.rf51) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e51n.sound RFChecks.e51n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e51n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e51n.left 0)=integerCoefficients (BasisData.rf51).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e51n.target0=affineShift (SourceBasis.rf51).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf51).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(258956978573803520:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf51).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(505775348776960:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(258956978573803520:ℤ)] (a-(83/256:ℝ))=(258956978573803520:ℝ) by simp [evalZ,horner]),(show evalZ [(505775348776960:ℤ)] (a-(83/256:ℝ))=(505775348776960:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf51] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf51).numerator.denominator = 505775348776960 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf51).numerator) (a-(83/256:ℝ)) /
      (505775348776960:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf51).numerator a
    simp only [SourceBasis.rf51]
    nlinarith [hh]
  · have hh := RFChecks.e51d.sound RFChecks.e51d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e51d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e51d.left 0)=factorCoefficients (BasisData.rf51).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e51d.target0=affineShift (SourceBasis.rf51).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf51).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf51).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ))=(2251799813685248:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf51] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf51).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf51).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf51).denominator a
    simp only [SourceBasis.rf51]
    nlinarith [hh]
  · norm_num [BasisData.rf51,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf52_translation (a : ℝ) :
    (BasisData.rf52).eval (a-83/256)=(SourceBasis.rf52).eval a := by
  apply translated_rf_of_scaled (BasisData.rf52) (SourceBasis.rf52) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e52n.sound RFChecks.e52n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e52n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e52n.left 0)=integerCoefficients (BasisData.rf52).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e52n.target0=affineShift (SourceBasis.rf52).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf52).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(258956978573803520:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf52).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(252887674388480:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(258956978573803520:ℤ)] (a-(83/256:ℝ))=(258956978573803520:ℝ) by simp [evalZ,horner]),(show evalZ [(252887674388480:ℤ)] (a-(83/256:ℝ))=(252887674388480:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf52] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf52).numerator.denominator = 252887674388480 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf52).numerator) (a-(83/256:ℝ)) /
      (252887674388480:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf52).numerator a
    simp only [SourceBasis.rf52]
    nlinarith [hh]
  · have hh := RFChecks.e52d.sound RFChecks.e52d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e52d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e52d.left 0)=factorCoefficients (BasisData.rf52).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e52d.target0=affineShift (SourceBasis.rf52).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf52).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf52).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ))=(2251799813685248:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf52] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf52).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf52).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf52).denominator a
    simp only [SourceBasis.rf52]
    nlinarith [hh]
  · norm_num [BasisData.rf52,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf53_translation (a : ℝ) :
    (BasisData.rf53).eval (a-83/256)=(SourceBasis.rf53).eval a := by
  apply translated_rf_of_scaled (BasisData.rf53) (SourceBasis.rf53) (1/1840:ℝ) (1/16:ℝ) a (83/256)
  · have hh := RFChecks.e53n.sound RFChecks.e53n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e53n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e53n.left 0)=integerCoefficients (BasisData.rf53).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e53n.target0=affineShift (SourceBasis.rf53).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf53).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(132585973029787402240:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf53).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(517913957147607040:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(132585973029787402240:ℤ)] (a-(83/256:ℝ))=(132585973029787402240:ℝ) by simp [evalZ,horner]),(show evalZ [(517913957147607040:ℤ)] (a-(83/256:ℝ))=(517913957147607040:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf53] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf53).numerator.denominator = 517913957147607040 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf53).numerator) (a-(83/256:ℝ)) /
      (517913957147607040:ℝ) = (1/1840:ℝ)*evalZ (SourceBasis.rf53).numerator a
    simp only [SourceBasis.rf53]
    nlinarith [hh]
  · have hh := RFChecks.e53d.sound RFChecks.e53d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e53d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e53d.left 0)=factorCoefficients (BasisData.rf53).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e53d.target0=affineShift (SourceBasis.rf53).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf53).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(4503599627370496:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf53).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(4503599627370496:ℤ)] (a-(83/256:ℝ))=(4503599627370496:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf53] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf53).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf53).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/16:ℝ)*evalZ (SourceBasis.rf53).denominator a
    simp only [SourceBasis.rf53]
    nlinarith [hh]
  · norm_num [BasisData.rf53,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf54_translation (a : ℝ) :
    (BasisData.rf54).eval (a-83/256)=(SourceBasis.rf54).eval a := by
  apply translated_rf_of_scaled (BasisData.rf54) (SourceBasis.rf54) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e54n.sound RFChecks.e54n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e54n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e54n.left 0)=integerCoefficients (BasisData.rf54).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e54n.target0=affineShift (SourceBasis.rf54).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf54).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(66292986514893701120:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf54).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(64739244643450880:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(66292986514893701120:ℤ)] (a-(83/256:ℝ))=(66292986514893701120:ℝ) by simp [evalZ,horner]),(show evalZ [(64739244643450880:ℤ)] (a-(83/256:ℝ))=(64739244643450880:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf54] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf54).numerator.denominator = 64739244643450880 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf54).numerator) (a-(83/256:ℝ)) /
      (64739244643450880:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf54).numerator a
    simp only [SourceBasis.rf54]
    nlinarith [hh]
  · have hh := RFChecks.e54d.sound RFChecks.e54d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e54d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e54d.left 0)=factorCoefficients (BasisData.rf54).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e54d.target0=affineShift (SourceBasis.rf54).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf54).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf54).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ))=(2251799813685248:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf54] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf54).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf54).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf54).denominator a
    simp only [SourceBasis.rf54]
    nlinarith [hh]
  · norm_num [BasisData.rf54,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf55_translation (a : ℝ) :
    (BasisData.rf55).eval (a-83/256)=(SourceBasis.rf55).eval a := by
  apply translated_rf_of_scaled (BasisData.rf55) (SourceBasis.rf55) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e55n.sound RFChecks.e55n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e55n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e55n.left 0)=integerCoefficients (BasisData.rf55).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e55n.target0=affineShift (SourceBasis.rf55).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf55).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(66292986514893701120:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf55).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(32369622321725440:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(66292986514893701120:ℤ)] (a-(83/256:ℝ))=(66292986514893701120:ℝ) by simp [evalZ,horner]),(show evalZ [(32369622321725440:ℤ)] (a-(83/256:ℝ))=(32369622321725440:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf55] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf55).numerator.denominator = 32369622321725440 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf55).numerator) (a-(83/256:ℝ)) /
      (32369622321725440:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf55).numerator a
    simp only [SourceBasis.rf55]
    nlinarith [hh]
  · have hh := RFChecks.e55d.sound RFChecks.e55d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e55d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e55d.left 0)=factorCoefficients (BasisData.rf55).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e55d.target0=affineShift (SourceBasis.rf55).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf55).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf55).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ))=(2251799813685248:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf55] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf55).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf55).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf55).denominator a
    simp only [SourceBasis.rf55]
    nlinarith [hh]
  · norm_num [BasisData.rf55,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf56_translation (a : ℝ) :
    (BasisData.rf56).eval (a-83/256)=(SourceBasis.rf56).eval a := by
  apply translated_rf_of_scaled (BasisData.rf56) (SourceBasis.rf56) (1/1840:ℝ) (1/16:ℝ) a (83/256)
  · have hh := RFChecks.e56n.sound RFChecks.e56n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e56n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e56n.left 0)=integerCoefficients (BasisData.rf56).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e56n.target0=affineShift (SourceBasis.rf56).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf56).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(33942009095625574973440:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf56).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(66292986514893701120:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(33942009095625574973440:ℤ)] (a-(83/256:ℝ))=(33942009095625574973440:ℝ) by simp [evalZ,horner]),(show evalZ [(66292986514893701120:ℤ)] (a-(83/256:ℝ))=(66292986514893701120:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf56] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf56).numerator.denominator = 66292986514893701120 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf56).numerator) (a-(83/256:ℝ)) /
      (66292986514893701120:ℝ) = (1/1840:ℝ)*evalZ (SourceBasis.rf56).numerator a
    simp only [SourceBasis.rf56]
    nlinarith [hh]
  · have hh := RFChecks.e56d.sound RFChecks.e56d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e56d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e56d.left 0)=factorCoefficients (BasisData.rf56).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e56d.target0=affineShift (SourceBasis.rf56).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf56).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(4503599627370496:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf56).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(4503599627370496:ℤ)] (a-(83/256:ℝ))=(4503599627370496:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf56] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf56).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf56).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/16:ℝ)*evalZ (SourceBasis.rf56).denominator a
    simp only [SourceBasis.rf56]
    nlinarith [hh]
  · norm_num [BasisData.rf56,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf57_translation (a : ℝ) :
    (BasisData.rf57).eval (a-83/256)=(SourceBasis.rf57).eval a := by
  apply translated_rf_of_scaled (BasisData.rf57) (SourceBasis.rf57) (1/1840:ℝ) (1/16:ℝ) a (83/256)
  · have hh := RFChecks.e57n.sound RFChecks.e57n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e57n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e57n.left 0)=integerCoefficients (BasisData.rf57).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e57n.target0=affineShift (SourceBasis.rf57).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf57).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(33942009095625574973440:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf57).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(33146493257446850560:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(33942009095625574973440:ℤ)] (a-(83/256:ℝ))=(33942009095625574973440:ℝ) by simp [evalZ,horner]),(show evalZ [(33146493257446850560:ℤ)] (a-(83/256:ℝ))=(33146493257446850560:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf57] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf57).numerator.denominator = 33146493257446850560 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf57).numerator) (a-(83/256:ℝ)) /
      (33146493257446850560:ℝ) = (1/1840:ℝ)*evalZ (SourceBasis.rf57).numerator a
    simp only [SourceBasis.rf57]
    nlinarith [hh]
  · have hh := RFChecks.e57d.sound RFChecks.e57d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e57d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e57d.left 0)=factorCoefficients (BasisData.rf57).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e57d.target0=affineShift (SourceBasis.rf57).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf57).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(4503599627370496:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf57).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(4503599627370496:ℤ)] (a-(83/256:ℝ))=(4503599627370496:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf57] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf57).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf57).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/16:ℝ)*evalZ (SourceBasis.rf57).denominator a
    simp only [SourceBasis.rf57]
    nlinarith [hh]
  · norm_num [BasisData.rf57,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf58_translation (a : ℝ) :
    (BasisData.rf58).eval (a-83/256)=(SourceBasis.rf58).eval a := by
  apply translated_rf_of_scaled (BasisData.rf58) (SourceBasis.rf58) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e58n.sound RFChecks.e58n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e58n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e58n.left 0)=integerCoefficients (BasisData.rf58).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e58n.target0=affineShift (SourceBasis.rf58).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf58).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(16971004547812787486720:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf58).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(1035827914295214080:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(16971004547812787486720:ℤ)] (a-(83/256:ℝ))=(16971004547812787486720:ℝ) by simp [evalZ,horner]),(show evalZ [(1035827914295214080:ℤ)] (a-(83/256:ℝ))=(1035827914295214080:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf58] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf58).numerator.denominator = 1035827914295214080 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf58).numerator) (a-(83/256:ℝ)) /
      (1035827914295214080:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf58).numerator a
    simp only [SourceBasis.rf58]
    nlinarith [hh]
  · have hh := RFChecks.e58d.sound RFChecks.e58d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e58d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e58d.left 0)=factorCoefficients (BasisData.rf58).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e58d.target0=affineShift (SourceBasis.rf58).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf58).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf58).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ))=(2251799813685248:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf58] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf58).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf58).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf58).denominator a
    simp only [SourceBasis.rf58]
    nlinarith [hh]
  · norm_num [BasisData.rf58,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf59_translation (a : ℝ) :
    (BasisData.rf59).eval (a-83/256)=(SourceBasis.rf59).eval a := by
  apply translated_rf_of_scaled (BasisData.rf59) (SourceBasis.rf59) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e59n.sound RFChecks.e59n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e59n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e59n.left 0)=integerCoefficients (BasisData.rf59).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e59n.target0=affineShift (SourceBasis.rf59).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf59).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(16971004547812787486720:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf59).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(16573246628723425280:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(16971004547812787486720:ℤ)] (a-(83/256:ℝ))=(16971004547812787486720:ℝ) by simp [evalZ,horner]),(show evalZ [(16573246628723425280:ℤ)] (a-(83/256:ℝ))=(16573246628723425280:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf59] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf59).numerator.denominator = 16573246628723425280 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf59).numerator) (a-(83/256:ℝ)) /
      (16573246628723425280:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf59).numerator a
    simp only [SourceBasis.rf59]
    nlinarith [hh]
  · have hh := RFChecks.e59d.sound RFChecks.e59d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e59d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e59d.left 0)=factorCoefficients (BasisData.rf59).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e59d.target0=affineShift (SourceBasis.rf59).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf59).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf59).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ))=(2251799813685248:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf59] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf59).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf59).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf59).denominator a
    simp only [SourceBasis.rf59]
    nlinarith [hh]
  · norm_num [BasisData.rf59,ThomsonNegative.Compact.Packed.qval]
  · norm_num

#print axioms rf50_translation
end ThomsonNegative.Certificate.Bridges
