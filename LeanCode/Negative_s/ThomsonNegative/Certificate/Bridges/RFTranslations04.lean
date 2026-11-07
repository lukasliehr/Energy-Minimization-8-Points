import ThomsonNegative.Certificate.Bridges.RFChecks04
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
theorem rf40_translation (a : ℝ) :
    (BasisData.rf40).eval (a-83/256)=(SourceBasis.rf40).eval a := by
  apply translated_rf_of_scaled (BasisData.rf40) (SourceBasis.rf40) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e40n.sound RFChecks.e40n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e40n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e40n.left 0)=integerCoefficients (BasisData.rf40).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e40n.target0=affineShift (SourceBasis.rf40).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf40).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(16971004547812787486720:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf40).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(33146493257446850560:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(16971004547812787486720:ℤ)] (a-(83/256:ℝ))=(16971004547812787486720:ℝ) by simp [evalZ,horner]),(show evalZ [(33146493257446850560:ℤ)] (a-(83/256:ℝ))=(33146493257446850560:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf40] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf40).numerator.denominator = 33146493257446850560 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf40).numerator) (a-(83/256:ℝ)) /
      (33146493257446850560:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf40).numerator a
    simp only [SourceBasis.rf40]
    nlinarith [hh]
  · have hh := RFChecks.e40d.sound RFChecks.e40d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e40d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e40d.left 0)=factorCoefficients (BasisData.rf40).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e40d.target0=affineShift (SourceBasis.rf40).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf40).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf40).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ))=(576460752303423488:ℝ) by simp [evalZ,horner]),(show evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))=(281474976710656:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf40] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf40).factors = 281474976710656 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf40).factors) (a-(83/256:ℝ)) /
      (281474976710656:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf40).denominator a
    simp only [SourceBasis.rf40]
    nlinarith [hh]
  · norm_num [BasisData.rf40,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf41_translation (a : ℝ) :
    (BasisData.rf41).eval (a-83/256)=(SourceBasis.rf41).eval a := by
  apply translated_rf_of_scaled (BasisData.rf41) (SourceBasis.rf41) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e41n.sound RFChecks.e41n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e41n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e41n.left 0)=integerCoefficients (BasisData.rf41).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e41n.target0=affineShift (SourceBasis.rf41).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf41).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(16971004547812787486720:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf41).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(8286623314361712640:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(16971004547812787486720:ℤ)] (a-(83/256:ℝ))=(16971004547812787486720:ℝ) by simp [evalZ,horner]),(show evalZ [(8286623314361712640:ℤ)] (a-(83/256:ℝ))=(8286623314361712640:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf41] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf41).numerator.denominator = 8286623314361712640 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf41).numerator) (a-(83/256:ℝ)) /
      (8286623314361712640:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf41).numerator a
    simp only [SourceBasis.rf41]
    nlinarith [hh]
  · have hh := RFChecks.e41d.sound RFChecks.e41d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e41d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e41d.left 0)=factorCoefficients (BasisData.rf41).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e41d.target0=affineShift (SourceBasis.rf41).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf41).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf41).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ))=(576460752303423488:ℝ) by simp [evalZ,horner]),(show evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))=(281474976710656:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf41] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf41).factors = 281474976710656 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf41).factors) (a-(83/256:ℝ)) /
      (281474976710656:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf41).denominator a
    simp only [SourceBasis.rf41]
    nlinarith [hh]
  · norm_num [BasisData.rf41,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf42_translation (a : ℝ) :
    (BasisData.rf42).eval (a-83/256)=(SourceBasis.rf42).eval a := by
  apply translated_rf_of_scaled (BasisData.rf42) (SourceBasis.rf42) (1/1840:ℝ) (1/16:ℝ) a (83/256)
  · have hh := RFChecks.e42n.sound RFChecks.e42n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e42n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e42n.left 0)=integerCoefficients (BasisData.rf42).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e42n.target0=affineShift (SourceBasis.rf42).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf42).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(8689154328480147193200640:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf42).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(33942009095625574973440:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(8689154328480147193200640:ℤ)] (a-(83/256:ℝ))=(8689154328480147193200640:ℝ) by simp [evalZ,horner]),(show evalZ [(33942009095625574973440:ℤ)] (a-(83/256:ℝ))=(33942009095625574973440:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf42] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf42).numerator.denominator = 33942009095625574973440 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf42).numerator) (a-(83/256:ℝ)) /
      (33942009095625574973440:ℝ) = (1/1840:ℝ)*evalZ (SourceBasis.rf42).numerator a
    simp only [SourceBasis.rf42]
    nlinarith [hh]
  · have hh := RFChecks.e42d.sound RFChecks.e42d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e42d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e42d.left 0)=factorCoefficients (BasisData.rf42).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e42d.target0=affineShift (SourceBasis.rf42).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf42).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1152921504606846976:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf42).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1152921504606846976:ℤ)] (a-(83/256:ℝ))=(1152921504606846976:ℝ) by simp [evalZ,horner]),(show evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))=(281474976710656:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf42] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf42).factors = 281474976710656 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf42).factors) (a-(83/256:ℝ)) /
      (281474976710656:ℝ) = (1/16:ℝ)*evalZ (SourceBasis.rf42).denominator a
    simp only [SourceBasis.rf42]
    nlinarith [hh]
  · norm_num [BasisData.rf42,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf43_translation (a : ℝ) :
    (BasisData.rf43).eval (a-83/256)=(SourceBasis.rf43).eval a := by
  apply translated_rf_of_scaled (BasisData.rf43) (SourceBasis.rf43) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e43n.sound RFChecks.e43n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e43n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e43n.left 0)=integerCoefficients (BasisData.rf43).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e43n.target0=affineShift (SourceBasis.rf43).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf43).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(4344577164240073596600320:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf43).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(1060687784238299217920:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(4344577164240073596600320:ℤ)] (a-(83/256:ℝ))=(4344577164240073596600320:ℝ) by simp [evalZ,horner]),(show evalZ [(1060687784238299217920:ℤ)] (a-(83/256:ℝ))=(1060687784238299217920:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf43] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf43).numerator.denominator = 1060687784238299217920 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf43).numerator) (a-(83/256:ℝ)) /
      (1060687784238299217920:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf43).numerator a
    simp only [SourceBasis.rf43]
    nlinarith [hh]
  · have hh := RFChecks.e43d.sound RFChecks.e43d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e43d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e43d.left 0)=factorCoefficients (BasisData.rf43).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e43d.target0=affineShift (SourceBasis.rf43).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf43).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf43).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ))=(576460752303423488:ℝ) by simp [evalZ,horner]),(show evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))=(281474976710656:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf43] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf43).factors = 281474976710656 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf43).factors) (a-(83/256:ℝ)) /
      (281474976710656:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf43).denominator a
    simp only [SourceBasis.rf43]
    nlinarith [hh]
  · norm_num [BasisData.rf43,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf44_translation (a : ℝ) :
    (BasisData.rf44).eval (a-83/256)=(SourceBasis.rf44).eval a := by
  apply translated_rf_of_scaled (BasisData.rf44) (SourceBasis.rf44) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e44n.sound RFChecks.e44n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e44n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e44n.left 0)=integerCoefficients (BasisData.rf44).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e44n.target0=affineShift (SourceBasis.rf44).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf44).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(4344577164240073596600320:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf44).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(2121375568476598435840:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(4344577164240073596600320:ℤ)] (a-(83/256:ℝ))=(4344577164240073596600320:ℝ) by simp [evalZ,horner]),(show evalZ [(2121375568476598435840:ℤ)] (a-(83/256:ℝ))=(2121375568476598435840:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf44] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf44).numerator.denominator = 2121375568476598435840 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf44).numerator) (a-(83/256:ℝ)) /
      (2121375568476598435840:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf44).numerator a
    simp only [SourceBasis.rf44]
    nlinarith [hh]
  · have hh := RFChecks.e44d.sound RFChecks.e44d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e44d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e44d.left 0)=factorCoefficients (BasisData.rf44).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e44d.target0=affineShift (SourceBasis.rf44).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf44).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf44).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ))=(576460752303423488:ℝ) by simp [evalZ,horner]),(show evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))=(281474976710656:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf44] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf44).factors = 281474976710656 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf44).factors) (a-(83/256:ℝ)) /
      (281474976710656:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf44).denominator a
    simp only [SourceBasis.rf44]
    nlinarith [hh]
  · norm_num [BasisData.rf44,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf45_translation (a : ℝ) :
    (BasisData.rf45).eval (a-83/256)=(SourceBasis.rf45).eval a := by
  apply translated_rf_of_scaled (BasisData.rf45) (SourceBasis.rf45) (1/1840:ℝ) (1/16:ℝ) a (83/256)
  · have hh := RFChecks.e45n.sound RFChecks.e45n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e45n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e45n.left 0)=integerCoefficients (BasisData.rf45).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e45n.target0=affineShift (SourceBasis.rf45).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf45).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2224423508090917681459363840:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf45).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(4344577164240073596600320:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2224423508090917681459363840:ℤ)] (a-(83/256:ℝ))=(2224423508090917681459363840:ℝ) by simp [evalZ,horner]),(show evalZ [(4344577164240073596600320:ℤ)] (a-(83/256:ℝ))=(4344577164240073596600320:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf45] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf45).numerator.denominator = 4344577164240073596600320 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf45).numerator) (a-(83/256:ℝ)) /
      (4344577164240073596600320:ℝ) = (1/1840:ℝ)*evalZ (SourceBasis.rf45).numerator a
    simp only [SourceBasis.rf45]
    nlinarith [hh]
  · have hh := RFChecks.e45d.sound RFChecks.e45d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e45d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e45d.left 0)=factorCoefficients (BasisData.rf45).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e45d.target0=affineShift (SourceBasis.rf45).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf45).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1152921504606846976:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf45).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1152921504606846976:ℤ)] (a-(83/256:ℝ))=(1152921504606846976:ℝ) by simp [evalZ,horner]),(show evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))=(281474976710656:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf45] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf45).factors = 281474976710656 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf45).factors) (a-(83/256:ℝ)) /
      (281474976710656:ℝ) = (1/16:ℝ)*evalZ (SourceBasis.rf45).denominator a
    simp only [SourceBasis.rf45]
    nlinarith [hh]
  · norm_num [BasisData.rf45,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf46_translation (a : ℝ) :
    (BasisData.rf46).eval (a-83/256)=(SourceBasis.rf46).eval a := by
  apply translated_rf_of_scaled (BasisData.rf46) (SourceBasis.rf46) (1/1840:ℝ) (1/16:ℝ) a (83/256)
  · have hh := RFChecks.e46n.sound RFChecks.e46n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e46n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e46n.left 0)=integerCoefficients (BasisData.rf46).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e46n.target0=affineShift (SourceBasis.rf46).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf46).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2224423508090917681459363840:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf46).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(2172288582120036798300160:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2224423508090917681459363840:ℤ)] (a-(83/256:ℝ))=(2224423508090917681459363840:ℝ) by simp [evalZ,horner]),(show evalZ [(2172288582120036798300160:ℤ)] (a-(83/256:ℝ))=(2172288582120036798300160:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf46] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf46).numerator.denominator = 2172288582120036798300160 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf46).numerator) (a-(83/256:ℝ)) /
      (2172288582120036798300160:ℝ) = (1/1840:ℝ)*evalZ (SourceBasis.rf46).numerator a
    simp only [SourceBasis.rf46]
    nlinarith [hh]
  · have hh := RFChecks.e46d.sound RFChecks.e46d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e46d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e46d.left 0)=factorCoefficients (BasisData.rf46).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e46d.target0=affineShift (SourceBasis.rf46).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf46).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1152921504606846976:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf46).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1152921504606846976:ℤ)] (a-(83/256:ℝ))=(1152921504606846976:ℝ) by simp [evalZ,horner]),(show evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))=(281474976710656:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf46] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf46).factors = 281474976710656 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf46).factors) (a-(83/256:ℝ)) /
      (281474976710656:ℝ) = (1/16:ℝ)*evalZ (SourceBasis.rf46).denominator a
    simp only [SourceBasis.rf46]
    nlinarith [hh]
  · norm_num [BasisData.rf46,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf47_translation (a : ℝ) :
    (BasisData.rf47).eval (a-83/256)=(SourceBasis.rf47).eval a := by
  apply translated_rf_of_scaled (BasisData.rf47) (SourceBasis.rf47) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e47n.sound RFChecks.e47n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e47n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e47n.left 0)=integerCoefficients (BasisData.rf47).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e47n.target0=affineShift (SourceBasis.rf47).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf47).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1112211754045458840729681920:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf47).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(67884018191251149946880:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1112211754045458840729681920:ℤ)] (a-(83/256:ℝ))=(1112211754045458840729681920:ℝ) by simp [evalZ,horner]),(show evalZ [(67884018191251149946880:ℤ)] (a-(83/256:ℝ))=(67884018191251149946880:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf47] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf47).numerator.denominator = 67884018191251149946880 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf47).numerator) (a-(83/256:ℝ)) /
      (67884018191251149946880:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf47).numerator a
    simp only [SourceBasis.rf47]
    nlinarith [hh]
  · have hh := RFChecks.e47d.sound RFChecks.e47d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e47d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e47d.left 0)=factorCoefficients (BasisData.rf47).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e47d.target0=affineShift (SourceBasis.rf47).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf47).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf47).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ))=(576460752303423488:ℝ) by simp [evalZ,horner]),(show evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))=(281474976710656:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf47] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf47).factors = 281474976710656 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf47).factors) (a-(83/256:ℝ)) /
      (281474976710656:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf47).denominator a
    simp only [SourceBasis.rf47]
    nlinarith [hh]
  · norm_num [BasisData.rf47,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf48_translation (a : ℝ) :
    (BasisData.rf48).eval (a-83/256)=(SourceBasis.rf48).eval a := by
  apply translated_rf_of_scaled (BasisData.rf48) (SourceBasis.rf48) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e48n.sound RFChecks.e48n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e48n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e48n.left 0)=integerCoefficients (BasisData.rf48).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e48n.target0=affineShift (SourceBasis.rf48).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf48).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1112211754045458840729681920:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf48).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(1086144291060018399150080:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1112211754045458840729681920:ℤ)] (a-(83/256:ℝ))=(1112211754045458840729681920:ℝ) by simp [evalZ,horner]),(show evalZ [(1086144291060018399150080:ℤ)] (a-(83/256:ℝ))=(1086144291060018399150080:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf48] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf48).numerator.denominator = 1086144291060018399150080 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf48).numerator) (a-(83/256:ℝ)) /
      (1086144291060018399150080:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf48).numerator a
    simp only [SourceBasis.rf48]
    nlinarith [hh]
  · have hh := RFChecks.e48d.sound RFChecks.e48d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e48d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e48d.left 0)=factorCoefficients (BasisData.rf48).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e48d.target0=affineShift (SourceBasis.rf48).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf48).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf48).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ))=(576460752303423488:ℝ) by simp [evalZ,horner]),(show evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))=(281474976710656:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf48] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf48).factors = 281474976710656 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf48).factors) (a-(83/256:ℝ)) /
      (281474976710656:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf48).denominator a
    simp only [SourceBasis.rf48]
    nlinarith [hh]
  · norm_num [BasisData.rf48,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf49_translation (a : ℝ) :
    (BasisData.rf49).eval (a-83/256)=(SourceBasis.rf49).eval a := by
  apply translated_rf_of_scaled (BasisData.rf49) (SourceBasis.rf49) (1:ℝ) (1:ℝ) a (83/256)
  · have hh := RFChecks.e49n.sound RFChecks.e49n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e49n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e49n.left 0)=integerCoefficients (BasisData.rf49).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e49n.target0=affineShift (SourceBasis.rf49).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf49).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(4294967296:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf49).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(16777216:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),(show evalZ [(16777216:ℤ)] (a-(83/256:ℝ))=(16777216:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf49] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf49).numerator.denominator = 16777216 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf49).numerator) (a-(83/256:ℝ)) /
      (16777216:ℝ) = (1:ℝ)*evalZ (SourceBasis.rf49).numerator a
    simp only [SourceBasis.rf49]
    nlinarith [hh]
  · have hh := RFChecks.e49d.sound RFChecks.e49d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e49d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e49d.left 0)=factorCoefficients (BasisData.rf49).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e49d.target0=affineShift (SourceBasis.rf49).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf49).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(256:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf49).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(256:ℤ)] (a-(83/256:ℝ))=(256:ℝ) by simp [evalZ,horner]),(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf49] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf49).factors = 1 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf49).factors) (a-(83/256:ℝ)) /
      (1:ℝ) = (1:ℝ)*evalZ (SourceBasis.rf49).denominator a
    simp only [SourceBasis.rf49]
    nlinarith [hh]
  · norm_num [BasisData.rf49,ThomsonNegative.Compact.Packed.qval]
  · norm_num

#print axioms rf40_translation
end ThomsonNegative.Certificate.Bridges
