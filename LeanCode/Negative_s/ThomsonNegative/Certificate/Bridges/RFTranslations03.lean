import ThomsonNegative.Certificate.Bridges.RFChecks03
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
theorem rf30_translation (a : ℝ) :
    (BasisData.rf30).eval (a-83/256)=(SourceBasis.rf30).eval a := by
  apply translated_rf_of_scaled (BasisData.rf30) (SourceBasis.rf30) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e30n.sound RFChecks.e30n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e30n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e30n.left 0)=integerCoefficients (BasisData.rf30).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e30n.target0=affineShift (SourceBasis.rf30).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf30).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(4344577164240073596600320:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf30).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(2121375568476598435840:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(4344577164240073596600320:ℤ)] (a-(83/256:ℝ))=(4344577164240073596600320:ℝ) by simp [evalZ,horner]),(show evalZ [(2121375568476598435840:ℤ)] (a-(83/256:ℝ))=(2121375568476598435840:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf30] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf30).numerator.denominator = 2121375568476598435840 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf30).numerator) (a-(83/256:ℝ)) /
      (2121375568476598435840:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf30).numerator a
    simp only [SourceBasis.rf30]
    nlinarith [hh]
  · have hh := RFChecks.e30d.sound RFChecks.e30d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e30d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e30d.left 0)=factorCoefficients (BasisData.rf30).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e30d.target0=affineShift (SourceBasis.rf30).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf30).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf30).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ))=(576460752303423488:ℝ) by simp [evalZ,horner]),(show evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))=(281474976710656:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf30] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf30).factors = 281474976710656 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf30).factors) (a-(83/256:ℝ)) /
      (281474976710656:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf30).denominator a
    simp only [SourceBasis.rf30]
    nlinarith [hh]
  · norm_num [BasisData.rf30,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf31_translation (a : ℝ) :
    (BasisData.rf31).eval (a-83/256)=(SourceBasis.rf31).eval a := by
  apply translated_rf_of_scaled (BasisData.rf31) (SourceBasis.rf31) (1/1840:ℝ) (1/16:ℝ) a (83/256)
  · have hh := RFChecks.e31n.sound RFChecks.e31n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e31n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e31n.left 0)=integerCoefficients (BasisData.rf31).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e31n.target0=affineShift (SourceBasis.rf31).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf31).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2224423508090917681459363840:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf31).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(8689154328480147193200640:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2224423508090917681459363840:ℤ)] (a-(83/256:ℝ))=(2224423508090917681459363840:ℝ) by simp [evalZ,horner]),(show evalZ [(8689154328480147193200640:ℤ)] (a-(83/256:ℝ))=(8689154328480147193200640:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf31] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf31).numerator.denominator = 8689154328480147193200640 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf31).numerator) (a-(83/256:ℝ)) /
      (8689154328480147193200640:ℝ) = (1/1840:ℝ)*evalZ (SourceBasis.rf31).numerator a
    simp only [SourceBasis.rf31]
    nlinarith [hh]
  · have hh := RFChecks.e31d.sound RFChecks.e31d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e31d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e31d.left 0)=factorCoefficients (BasisData.rf31).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e31d.target0=affineShift (SourceBasis.rf31).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf31).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1152921504606846976:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf31).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1152921504606846976:ℤ)] (a-(83/256:ℝ))=(1152921504606846976:ℝ) by simp [evalZ,horner]),(show evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))=(281474976710656:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf31] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf31).factors = 281474976710656 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf31).factors) (a-(83/256:ℝ)) /
      (281474976710656:ℝ) = (1/16:ℝ)*evalZ (SourceBasis.rf31).denominator a
    simp only [SourceBasis.rf31]
    nlinarith [hh]
  · norm_num [BasisData.rf31,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf32_translation (a : ℝ) :
    (BasisData.rf32).eval (a-83/256)=(SourceBasis.rf32).eval a := by
  apply translated_rf_of_scaled (BasisData.rf32) (SourceBasis.rf32) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e32n.sound RFChecks.e32n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e32n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e32n.left 0)=integerCoefficients (BasisData.rf32).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e32n.target0=affineShift (SourceBasis.rf32).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf32).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1112211754045458840729681920:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf32).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(271536072765004599787520:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1112211754045458840729681920:ℤ)] (a-(83/256:ℝ))=(1112211754045458840729681920:ℝ) by simp [evalZ,horner]),(show evalZ [(271536072765004599787520:ℤ)] (a-(83/256:ℝ))=(271536072765004599787520:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf32] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf32).numerator.denominator = 271536072765004599787520 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf32).numerator) (a-(83/256:ℝ)) /
      (271536072765004599787520:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf32).numerator a
    simp only [SourceBasis.rf32]
    nlinarith [hh]
  · have hh := RFChecks.e32d.sound RFChecks.e32d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e32d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e32d.left 0)=factorCoefficients (BasisData.rf32).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e32d.target0=affineShift (SourceBasis.rf32).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf32).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf32).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ))=(576460752303423488:ℝ) by simp [evalZ,horner]),(show evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))=(281474976710656:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf32] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf32).factors = 281474976710656 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf32).factors) (a-(83/256:ℝ)) /
      (281474976710656:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf32).denominator a
    simp only [SourceBasis.rf32]
    nlinarith [hh]
  · norm_num [BasisData.rf32,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf33_translation (a : ℝ) :
    (BasisData.rf33).eval (a-83/256)=(SourceBasis.rf33).eval a := by
  apply translated_rf_of_scaled (BasisData.rf33) (SourceBasis.rf33) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e33n.sound RFChecks.e33n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e33n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e33n.left 0)=integerCoefficients (BasisData.rf33).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e33n.target0=affineShift (SourceBasis.rf33).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf33).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1112211754045458840729681920:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf33).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(67884018191251149946880:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1112211754045458840729681920:ℤ)] (a-(83/256:ℝ))=(1112211754045458840729681920:ℝ) by simp [evalZ,horner]),(show evalZ [(67884018191251149946880:ℤ)] (a-(83/256:ℝ))=(67884018191251149946880:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf33] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf33).numerator.denominator = 67884018191251149946880 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf33).numerator) (a-(83/256:ℝ)) /
      (67884018191251149946880:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf33).numerator a
    simp only [SourceBasis.rf33]
    nlinarith [hh]
  · have hh := RFChecks.e33d.sound RFChecks.e33d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e33d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e33d.left 0)=factorCoefficients (BasisData.rf33).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e33d.target0=affineShift (SourceBasis.rf33).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf33).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf33).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ))=(576460752303423488:ℝ) by simp [evalZ,horner]),(show evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))=(281474976710656:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf33] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf33).factors = 281474976710656 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf33).factors) (a-(83/256:ℝ)) /
      (281474976710656:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf33).denominator a
    simp only [SourceBasis.rf33]
    nlinarith [hh]
  · norm_num [BasisData.rf33,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf34_translation (a : ℝ) :
    (BasisData.rf34).eval (a-83/256)=(SourceBasis.rf34).eval a := by
  apply translated_rf_of_scaled (BasisData.rf34) (SourceBasis.rf34) (1/1840:ℝ) (1/16:ℝ) a (83/256)
  · have hh := RFChecks.e34n.sound RFChecks.e34n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e34n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e34n.left 0)=integerCoefficients (BasisData.rf34).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e34n.target0=affineShift (SourceBasis.rf34).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf34).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(569452418071274926453597143040:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf34).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(1112211754045458840729681920:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(569452418071274926453597143040:ℤ)] (a-(83/256:ℝ))=(569452418071274926453597143040:ℝ) by simp [evalZ,horner]),(show evalZ [(1112211754045458840729681920:ℤ)] (a-(83/256:ℝ))=(1112211754045458840729681920:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf34] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf34).numerator.denominator = 1112211754045458840729681920 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf34).numerator) (a-(83/256:ℝ)) /
      (1112211754045458840729681920:ℝ) = (1/1840:ℝ)*evalZ (SourceBasis.rf34).numerator a
    simp only [SourceBasis.rf34]
    nlinarith [hh]
  · have hh := RFChecks.e34d.sound RFChecks.e34d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e34d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e34d.left 0)=factorCoefficients (BasisData.rf34).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e34d.target0=affineShift (SourceBasis.rf34).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf34).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1152921504606846976:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf34).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1152921504606846976:ℤ)] (a-(83/256:ℝ))=(1152921504606846976:ℝ) by simp [evalZ,horner]),(show evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))=(281474976710656:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf34] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf34).factors = 281474976710656 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf34).factors) (a-(83/256:ℝ)) /
      (281474976710656:ℝ) = (1/16:ℝ)*evalZ (SourceBasis.rf34).denominator a
    simp only [SourceBasis.rf34]
    nlinarith [hh]
  · norm_num [BasisData.rf34,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf35_translation (a : ℝ) :
    (BasisData.rf35).eval (a-83/256)=(SourceBasis.rf35).eval a := by
  apply translated_rf_of_scaled (BasisData.rf35) (SourceBasis.rf35) (1/1840:ℝ) (1/16:ℝ) a (83/256)
  · have hh := RFChecks.e35n.sound RFChecks.e35n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e35n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e35n.left 0)=integerCoefficients (BasisData.rf35).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e35n.target0=affineShift (SourceBasis.rf35).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf35).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(569452418071274926453597143040:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf35).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(8689154328480147193200640:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(569452418071274926453597143040:ℤ)] (a-(83/256:ℝ))=(569452418071274926453597143040:ℝ) by simp [evalZ,horner]),(show evalZ [(8689154328480147193200640:ℤ)] (a-(83/256:ℝ))=(8689154328480147193200640:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf35] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf35).numerator.denominator = 8689154328480147193200640 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf35).numerator) (a-(83/256:ℝ)) /
      (8689154328480147193200640:ℝ) = (1/1840:ℝ)*evalZ (SourceBasis.rf35).numerator a
    simp only [SourceBasis.rf35]
    nlinarith [hh]
  · have hh := RFChecks.e35d.sound RFChecks.e35d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e35d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e35d.left 0)=factorCoefficients (BasisData.rf35).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e35d.target0=affineShift (SourceBasis.rf35).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf35).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1152921504606846976:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf35).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1152921504606846976:ℤ)] (a-(83/256:ℝ))=(1152921504606846976:ℝ) by simp [evalZ,horner]),(show evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))=(281474976710656:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf35] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf35).factors = 281474976710656 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf35).factors) (a-(83/256:ℝ)) /
      (281474976710656:ℝ) = (1/16:ℝ)*evalZ (SourceBasis.rf35).denominator a
    simp only [SourceBasis.rf35]
    nlinarith [hh]
  · norm_num [BasisData.rf35,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf36_translation (a : ℝ) :
    (BasisData.rf36).eval (a-83/256)=(SourceBasis.rf36).eval a := by
  apply translated_rf_of_scaled (BasisData.rf36) (SourceBasis.rf36) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e36n.sound RFChecks.e36n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e36n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e36n.left 0)=integerCoefficients (BasisData.rf36).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e36n.target0=affineShift (SourceBasis.rf36).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf36).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(284726209035637463226798571520:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf36).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(17378308656960294386401280:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(284726209035637463226798571520:ℤ)] (a-(83/256:ℝ))=(284726209035637463226798571520:ℝ) by simp [evalZ,horner]),(show evalZ [(17378308656960294386401280:ℤ)] (a-(83/256:ℝ))=(17378308656960294386401280:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf36] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf36).numerator.denominator = 17378308656960294386401280 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf36).numerator) (a-(83/256:ℝ)) /
      (17378308656960294386401280:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf36).numerator a
    simp only [SourceBasis.rf36]
    nlinarith [hh]
  · have hh := RFChecks.e36d.sound RFChecks.e36d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e36d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e36d.left 0)=factorCoefficients (BasisData.rf36).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e36d.target0=affineShift (SourceBasis.rf36).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf36).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf36).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ))=(576460752303423488:ℝ) by simp [evalZ,horner]),(show evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))=(281474976710656:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf36] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf36).factors = 281474976710656 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf36).factors) (a-(83/256:ℝ)) /
      (281474976710656:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf36).denominator a
    simp only [SourceBasis.rf36]
    nlinarith [hh]
  · norm_num [BasisData.rf36,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf37_translation (a : ℝ) :
    (BasisData.rf37).eval (a-83/256)=(SourceBasis.rf37).eval a := by
  apply translated_rf_of_scaled (BasisData.rf37) (SourceBasis.rf37) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e37n.sound RFChecks.e37n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e37n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e37n.left 0)=integerCoefficients (BasisData.rf37).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e37n.target0=affineShift (SourceBasis.rf37).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf37).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(284726209035637463226798571520:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf37).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(69513234627841177545605120:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(284726209035637463226798571520:ℤ)] (a-(83/256:ℝ))=(284726209035637463226798571520:ℝ) by simp [evalZ,horner]),(show evalZ [(69513234627841177545605120:ℤ)] (a-(83/256:ℝ))=(69513234627841177545605120:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf37] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf37).numerator.denominator = 69513234627841177545605120 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf37).numerator) (a-(83/256:ℝ)) /
      (69513234627841177545605120:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf37).numerator a
    simp only [SourceBasis.rf37]
    nlinarith [hh]
  · have hh := RFChecks.e37d.sound RFChecks.e37d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e37d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e37d.left 0)=factorCoefficients (BasisData.rf37).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e37d.target0=affineShift (SourceBasis.rf37).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf37).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf37).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ))=(576460752303423488:ℝ) by simp [evalZ,horner]),(show evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))=(281474976710656:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf37] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf37).factors = 281474976710656 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf37).factors) (a-(83/256:ℝ)) /
      (281474976710656:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf37).denominator a
    simp only [SourceBasis.rf37]
    nlinarith [hh]
  · norm_num [BasisData.rf37,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf38_translation (a : ℝ) :
    (BasisData.rf38).eval (a-83/256)=(SourceBasis.rf38).eval a := by
  apply translated_rf_of_scaled (BasisData.rf38) (SourceBasis.rf38) (1:ℝ) (1:ℝ) a (83/256)
  · have hh := RFChecks.e38n.sound RFChecks.e38n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e38n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e38n.left 0)=integerCoefficients (BasisData.rf38).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e38n.target0=affineShift (SourceBasis.rf38).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf38).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf38).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(1073741824:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),(show evalZ [(1073741824:ℤ)] (a-(83/256:ℝ))=(1073741824:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf38] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf38).numerator.denominator = 1073741824 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf38).numerator) (a-(83/256:ℝ)) /
      (1073741824:ℝ) = (1:ℝ)*evalZ (SourceBasis.rf38).numerator a
    simp only [SourceBasis.rf38]
    nlinarith [hh]
  · have hh := RFChecks.e38d.sound RFChecks.e38d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e38d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e38d.left 0)=factorCoefficients (BasisData.rf38).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e38d.target0=affineShift (SourceBasis.rf38).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf38).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(256:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf38).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(256:ℤ)] (a-(83/256:ℝ))=(256:ℝ) by simp [evalZ,horner]),(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf38] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf38).factors = 1 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf38).factors) (a-(83/256:ℝ)) /
      (1:ℝ) = (1:ℝ)*evalZ (SourceBasis.rf38).denominator a
    simp only [SourceBasis.rf38]
    nlinarith [hh]
  · norm_num [BasisData.rf38,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf39_translation (a : ℝ) :
    (BasisData.rf39).eval (a-83/256)=(SourceBasis.rf39).eval a := by
  apply translated_rf_of_scaled (BasisData.rf39) (SourceBasis.rf39) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e39n.sound RFChecks.e39n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e39n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e39n.left 0)=integerCoefficients (BasisData.rf39).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e39n.target0=affineShift (SourceBasis.rf39).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf39).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(66292986514893701120:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf39).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(258956978573803520:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(66292986514893701120:ℤ)] (a-(83/256:ℝ))=(66292986514893701120:ℝ) by simp [evalZ,horner]),(show evalZ [(258956978573803520:ℤ)] (a-(83/256:ℝ))=(258956978573803520:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf39] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf39).numerator.denominator = 258956978573803520 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf39).numerator) (a-(83/256:ℝ)) /
      (258956978573803520:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf39).numerator a
    simp only [SourceBasis.rf39]
    nlinarith [hh]
  · have hh := RFChecks.e39d.sound RFChecks.e39d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e39d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e39d.left 0)=factorCoefficients (BasisData.rf39).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e39d.target0=affineShift (SourceBasis.rf39).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf39).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf39).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ))=(576460752303423488:ℝ) by simp [evalZ,horner]),(show evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))=(281474976710656:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf39] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf39).factors = 281474976710656 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf39).factors) (a-(83/256:ℝ)) /
      (281474976710656:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf39).denominator a
    simp only [SourceBasis.rf39]
    nlinarith [hh]
  · norm_num [BasisData.rf39,ThomsonNegative.Compact.Packed.qval]
  · norm_num

#print axioms rf30_translation
end ThomsonNegative.Certificate.Bridges
