import ThomsonNegative.Certificate.Bridges.RFChecks06
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
theorem rf60_translation (a : ℝ) :
    (BasisData.rf60).eval (a-83/256)=(SourceBasis.rf60).eval a := by
  apply translated_rf_of_scaled (BasisData.rf60) (SourceBasis.rf60) (1:ℝ) (1:ℝ) a (83/256)
  · have hh := RFChecks.e60n.sound RFChecks.e60n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e60n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e60n.left 0)=integerCoefficients (BasisData.rf60).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e60n.target0=affineShift (SourceBasis.rf60).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf60).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(16777216:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf60).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(65536:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(16777216:ℤ)] (a-(83/256:ℝ))=(16777216:ℝ) by simp [evalZ,horner]),(show evalZ [(65536:ℤ)] (a-(83/256:ℝ))=(65536:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf60] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf60).numerator.denominator = 65536 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf60).numerator) (a-(83/256:ℝ)) /
      (65536:ℝ) = (1:ℝ)*evalZ (SourceBasis.rf60).numerator a
    simp only [SourceBasis.rf60]
    nlinarith [hh]
  · have hh := RFChecks.e60d.sound RFChecks.e60d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e60d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e60d.left 0)=factorCoefficients (BasisData.rf60).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e60d.target0=affineShift (SourceBasis.rf60).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf60).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(256:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf60).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(256:ℤ)] (a-(83/256:ℝ))=(256:ℝ) by simp [evalZ,horner]),(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf60] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf60).factors = 1 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf60).factors) (a-(83/256:ℝ)) /
      (1:ℝ) = (1:ℝ)*evalZ (SourceBasis.rf60).denominator a
    simp only [SourceBasis.rf60]
    nlinarith [hh]
  · norm_num [BasisData.rf60,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf61_translation (a : ℝ) :
    (BasisData.rf61).eval (a-83/256)=(SourceBasis.rf61).eval a := by
  apply translated_rf_of_scaled (BasisData.rf61) (SourceBasis.rf61) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e61n.sound RFChecks.e61n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e61n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e61n.left 0)=integerCoefficients (BasisData.rf61).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e61n.target0=affineShift (SourceBasis.rf61).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf61).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1011550697553920:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf61).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(3951369912320:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1011550697553920:ℤ)] (a-(83/256:ℝ))=(1011550697553920:ℝ) by simp [evalZ,horner]),(show evalZ [(3951369912320:ℤ)] (a-(83/256:ℝ))=(3951369912320:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf61] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf61).numerator.denominator = 3951369912320 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf61).numerator) (a-(83/256:ℝ)) /
      (3951369912320:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf61).numerator a
    simp only [SourceBasis.rf61]
    nlinarith [hh]
  · have hh := RFChecks.e61d.sound RFChecks.e61d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e61d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e61d.left 0)=factorCoefficients (BasisData.rf61).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e61d.target0=affineShift (SourceBasis.rf61).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf61).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf61).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ))=(576460752303423488:ℝ) by simp [evalZ,horner]),(show evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))=(281474976710656:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf61] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf61).factors = 281474976710656 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf61).factors) (a-(83/256:ℝ)) /
      (281474976710656:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf61).denominator a
    simp only [SourceBasis.rf61]
    nlinarith [hh]
  · norm_num [BasisData.rf61,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf62_translation (a : ℝ) :
    (BasisData.rf62).eval (a-83/256)=(SourceBasis.rf62).eval a := by
  apply translated_rf_of_scaled (BasisData.rf62) (SourceBasis.rf62) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e62n.sound RFChecks.e62n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e62n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e62n.left 0)=integerCoefficients (BasisData.rf62).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e62n.target0=affineShift (SourceBasis.rf62).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf62).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(258956978573803520:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf62).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(505775348776960:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(258956978573803520:ℤ)] (a-(83/256:ℝ))=(258956978573803520:ℝ) by simp [evalZ,horner]),(show evalZ [(505775348776960:ℤ)] (a-(83/256:ℝ))=(505775348776960:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf62] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf62).numerator.denominator = 505775348776960 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf62).numerator) (a-(83/256:ℝ)) /
      (505775348776960:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf62).numerator a
    simp only [SourceBasis.rf62]
    nlinarith [hh]
  · have hh := RFChecks.e62d.sound RFChecks.e62d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e62d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e62d.left 0)=factorCoefficients (BasisData.rf62).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e62d.target0=affineShift (SourceBasis.rf62).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf62).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf62).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ))=(576460752303423488:ℝ) by simp [evalZ,horner]),(show evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))=(281474976710656:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf62] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf62).factors = 281474976710656 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf62).factors) (a-(83/256:ℝ)) /
      (281474976710656:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf62).denominator a
    simp only [SourceBasis.rf62]
    nlinarith [hh]
  · norm_num [BasisData.rf62,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf63_translation (a : ℝ) :
    (BasisData.rf63).eval (a-83/256)=(SourceBasis.rf63).eval a := by
  apply translated_rf_of_scaled (BasisData.rf63) (SourceBasis.rf63) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e63n.sound RFChecks.e63n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e63n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e63n.left 0)=integerCoefficients (BasisData.rf63).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e63n.target0=affineShift (SourceBasis.rf63).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf63).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(258956978573803520:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf63).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(63221918597120:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(258956978573803520:ℤ)] (a-(83/256:ℝ))=(258956978573803520:ℝ) by simp [evalZ,horner]),(show evalZ [(63221918597120:ℤ)] (a-(83/256:ℝ))=(63221918597120:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf63] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf63).numerator.denominator = 63221918597120 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf63).numerator) (a-(83/256:ℝ)) /
      (63221918597120:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf63).numerator a
    simp only [SourceBasis.rf63]
    nlinarith [hh]
  · have hh := RFChecks.e63d.sound RFChecks.e63d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e63d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e63d.left 0)=factorCoefficients (BasisData.rf63).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e63d.target0=affineShift (SourceBasis.rf63).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf63).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf63).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ))=(576460752303423488:ℝ) by simp [evalZ,horner]),(show evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))=(281474976710656:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf63] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf63).factors = 281474976710656 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf63).factors) (a-(83/256:ℝ)) /
      (281474976710656:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf63).denominator a
    simp only [SourceBasis.rf63]
    nlinarith [hh]
  · norm_num [BasisData.rf63,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf64_translation (a : ℝ) :
    (BasisData.rf64).eval (a-83/256)=(SourceBasis.rf64).eval a := by
  apply translated_rf_of_scaled (BasisData.rf64) (SourceBasis.rf64) (1/1840:ℝ) (1/16:ℝ) a (83/256)
  · have hh := RFChecks.e64n.sound RFChecks.e64n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e64n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e64n.left 0)=integerCoefficients (BasisData.rf64).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e64n.target0=affineShift (SourceBasis.rf64).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf64).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(132585973029787402240:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf64).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(517913957147607040:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(132585973029787402240:ℤ)] (a-(83/256:ℝ))=(132585973029787402240:ℝ) by simp [evalZ,horner]),(show evalZ [(517913957147607040:ℤ)] (a-(83/256:ℝ))=(517913957147607040:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf64] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf64).numerator.denominator = 517913957147607040 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf64).numerator) (a-(83/256:ℝ)) /
      (517913957147607040:ℝ) = (1/1840:ℝ)*evalZ (SourceBasis.rf64).numerator a
    simp only [SourceBasis.rf64]
    nlinarith [hh]
  · have hh := RFChecks.e64d.sound RFChecks.e64d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e64d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e64d.left 0)=factorCoefficients (BasisData.rf64).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e64d.target0=affineShift (SourceBasis.rf64).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf64).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1152921504606846976:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf64).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1152921504606846976:ℤ)] (a-(83/256:ℝ))=(1152921504606846976:ℝ) by simp [evalZ,horner]),(show evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))=(281474976710656:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf64] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf64).factors = 281474976710656 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf64).factors) (a-(83/256:ℝ)) /
      (281474976710656:ℝ) = (1/16:ℝ)*evalZ (SourceBasis.rf64).denominator a
    simp only [SourceBasis.rf64]
    nlinarith [hh]
  · norm_num [BasisData.rf64,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf65_translation (a : ℝ) :
    (BasisData.rf65).eval (a-83/256)=(SourceBasis.rf65).eval a := by
  apply translated_rf_of_scaled (BasisData.rf65) (SourceBasis.rf65) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e65n.sound RFChecks.e65n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e65n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e65n.left 0)=integerCoefficients (BasisData.rf65).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e65n.target0=affineShift (SourceBasis.rf65).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf65).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(66292986514893701120:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf65).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(16184811160862720:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(66292986514893701120:ℤ)] (a-(83/256:ℝ))=(66292986514893701120:ℝ) by simp [evalZ,horner]),(show evalZ [(16184811160862720:ℤ)] (a-(83/256:ℝ))=(16184811160862720:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf65] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf65).numerator.denominator = 16184811160862720 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf65).numerator) (a-(83/256:ℝ)) /
      (16184811160862720:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf65).numerator a
    simp only [SourceBasis.rf65]
    nlinarith [hh]
  · have hh := RFChecks.e65d.sound RFChecks.e65d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e65d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e65d.left 0)=factorCoefficients (BasisData.rf65).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e65d.target0=affineShift (SourceBasis.rf65).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf65).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf65).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ))=(576460752303423488:ℝ) by simp [evalZ,horner]),(show evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))=(281474976710656:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf65] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf65).factors = 281474976710656 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf65).factors) (a-(83/256:ℝ)) /
      (281474976710656:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf65).denominator a
    simp only [SourceBasis.rf65]
    nlinarith [hh]
  · norm_num [BasisData.rf65,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf66_translation (a : ℝ) :
    (BasisData.rf66).eval (a-83/256)=(SourceBasis.rf66).eval a := by
  apply translated_rf_of_scaled (BasisData.rf66) (SourceBasis.rf66) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e66n.sound RFChecks.e66n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e66n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e66n.left 0)=integerCoefficients (BasisData.rf66).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e66n.target0=affineShift (SourceBasis.rf66).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf66).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(66292986514893701120:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf66).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(64739244643450880:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(66292986514893701120:ℤ)] (a-(83/256:ℝ))=(66292986514893701120:ℝ) by simp [evalZ,horner]),(show evalZ [(64739244643450880:ℤ)] (a-(83/256:ℝ))=(64739244643450880:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf66] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf66).numerator.denominator = 64739244643450880 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf66).numerator) (a-(83/256:ℝ)) /
      (64739244643450880:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf66).numerator a
    simp only [SourceBasis.rf66]
    nlinarith [hh]
  · have hh := RFChecks.e66d.sound RFChecks.e66d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e66d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e66d.left 0)=factorCoefficients (BasisData.rf66).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e66d.target0=affineShift (SourceBasis.rf66).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf66).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf66).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ))=(576460752303423488:ℝ) by simp [evalZ,horner]),(show evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))=(281474976710656:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf66] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf66).factors = 281474976710656 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf66).factors) (a-(83/256:ℝ)) /
      (281474976710656:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf66).denominator a
    simp only [SourceBasis.rf66]
    nlinarith [hh]
  · norm_num [BasisData.rf66,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf67_translation (a : ℝ) :
    (BasisData.rf67).eval (a-83/256)=(SourceBasis.rf67).eval a := by
  apply translated_rf_of_scaled (BasisData.rf67) (SourceBasis.rf67) (1/1840:ℝ) (1/16:ℝ) a (83/256)
  · have hh := RFChecks.e67n.sound RFChecks.e67n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e67n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e67n.left 0)=integerCoefficients (BasisData.rf67).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e67n.target0=affineShift (SourceBasis.rf67).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf67).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(33942009095625574973440:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf67).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(66292986514893701120:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(33942009095625574973440:ℤ)] (a-(83/256:ℝ))=(33942009095625574973440:ℝ) by simp [evalZ,horner]),(show evalZ [(66292986514893701120:ℤ)] (a-(83/256:ℝ))=(66292986514893701120:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf67] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf67).numerator.denominator = 66292986514893701120 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf67).numerator) (a-(83/256:ℝ)) /
      (66292986514893701120:ℝ) = (1/1840:ℝ)*evalZ (SourceBasis.rf67).numerator a
    simp only [SourceBasis.rf67]
    nlinarith [hh]
  · have hh := RFChecks.e67d.sound RFChecks.e67d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e67d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e67d.left 0)=factorCoefficients (BasisData.rf67).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e67d.target0=affineShift (SourceBasis.rf67).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf67).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1152921504606846976:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf67).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1152921504606846976:ℤ)] (a-(83/256:ℝ))=(1152921504606846976:ℝ) by simp [evalZ,horner]),(show evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))=(281474976710656:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf67] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf67).factors = 281474976710656 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf67).factors) (a-(83/256:ℝ)) /
      (281474976710656:ℝ) = (1/16:ℝ)*evalZ (SourceBasis.rf67).denominator a
    simp only [SourceBasis.rf67]
    nlinarith [hh]
  · norm_num [BasisData.rf67,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf68_translation (a : ℝ) :
    (BasisData.rf68).eval (a-83/256)=(SourceBasis.rf68).eval a := by
  apply translated_rf_of_scaled (BasisData.rf68) (SourceBasis.rf68) (1/1840:ℝ) (1/16:ℝ) a (83/256)
  · have hh := RFChecks.e68n.sound RFChecks.e68n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e68n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e68n.left 0)=integerCoefficients (BasisData.rf68).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e68n.target0=affineShift (SourceBasis.rf68).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf68).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(33942009095625574973440:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf68).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(33146493257446850560:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(33942009095625574973440:ℤ)] (a-(83/256:ℝ))=(33942009095625574973440:ℝ) by simp [evalZ,horner]),(show evalZ [(33146493257446850560:ℤ)] (a-(83/256:ℝ))=(33146493257446850560:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf68] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf68).numerator.denominator = 33146493257446850560 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf68).numerator) (a-(83/256:ℝ)) /
      (33146493257446850560:ℝ) = (1/1840:ℝ)*evalZ (SourceBasis.rf68).numerator a
    simp only [SourceBasis.rf68]
    nlinarith [hh]
  · have hh := RFChecks.e68d.sound RFChecks.e68d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e68d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e68d.left 0)=factorCoefficients (BasisData.rf68).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e68d.target0=affineShift (SourceBasis.rf68).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf68).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1152921504606846976:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf68).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1152921504606846976:ℤ)] (a-(83/256:ℝ))=(1152921504606846976:ℝ) by simp [evalZ,horner]),(show evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))=(281474976710656:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf68] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf68).factors = 281474976710656 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf68).factors) (a-(83/256:ℝ)) /
      (281474976710656:ℝ) = (1/16:ℝ)*evalZ (SourceBasis.rf68).denominator a
    simp only [SourceBasis.rf68]
    nlinarith [hh]
  · norm_num [BasisData.rf68,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf69_translation (a : ℝ) :
    (BasisData.rf69).eval (a-83/256)=(SourceBasis.rf69).eval a := by
  apply translated_rf_of_scaled (BasisData.rf69) (SourceBasis.rf69) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e69n.sound RFChecks.e69n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e69n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e69n.left 0)=integerCoefficients (BasisData.rf69).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e69n.target0=affineShift (SourceBasis.rf69).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf69).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(16971004547812787486720:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf69).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(16573246628723425280:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(16971004547812787486720:ℤ)] (a-(83/256:ℝ))=(16971004547812787486720:ℝ) by simp [evalZ,horner]),(show evalZ [(16573246628723425280:ℤ)] (a-(83/256:ℝ))=(16573246628723425280:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf69] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf69).numerator.denominator = 16573246628723425280 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf69).numerator) (a-(83/256:ℝ)) /
      (16573246628723425280:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf69).numerator a
    simp only [SourceBasis.rf69]
    nlinarith [hh]
  · have hh := RFChecks.e69d.sound RFChecks.e69d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e69d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e69d.left 0)=factorCoefficients (BasisData.rf69).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e69d.target0=affineShift (SourceBasis.rf69).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf69).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf69).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ))=(576460752303423488:ℝ) by simp [evalZ,horner]),(show evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))=(281474976710656:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf69] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf69).factors = 281474976710656 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf69).factors) (a-(83/256:ℝ)) /
      (281474976710656:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf69).denominator a
    simp only [SourceBasis.rf69]
    nlinarith [hh]
  · norm_num [BasisData.rf69,ThomsonNegative.Compact.Packed.qval]
  · norm_num

#print axioms rf60_translation
end ThomsonNegative.Certificate.Bridges
