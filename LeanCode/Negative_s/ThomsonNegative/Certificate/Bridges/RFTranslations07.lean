import ThomsonNegative.Certificate.Bridges.RFChecks07
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
theorem rf70_translation (a : ℝ) :
    (BasisData.rf70).eval (a-83/256)=(SourceBasis.rf70).eval a := by
  apply translated_rf_of_scaled (BasisData.rf70) (SourceBasis.rf70) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e70n.sound RFChecks.e70n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e70n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e70n.left 0)=integerCoefficients (BasisData.rf70).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e70n.target0=affineShift (SourceBasis.rf70).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf70).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(16971004547812787486720:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf70).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(16573246628723425280:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(16971004547812787486720:ℤ)] (a-(83/256:ℝ))=(16971004547812787486720:ℝ) by simp [evalZ,horner]),(show evalZ [(16573246628723425280:ℤ)] (a-(83/256:ℝ))=(16573246628723425280:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf70] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf70).numerator.denominator = 16573246628723425280 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf70).numerator) (a-(83/256:ℝ)) /
      (16573246628723425280:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf70).numerator a
    simp only [SourceBasis.rf70]
    nlinarith [hh]
  · have hh := RFChecks.e70d.sound RFChecks.e70d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e70d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e70d.left 0)=factorCoefficients (BasisData.rf70).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e70d.target0=affineShift (SourceBasis.rf70).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf70).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf70).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ))=(576460752303423488:ℝ) by simp [evalZ,horner]),(show evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))=(281474976710656:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf70] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf70).factors = 281474976710656 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf70).factors) (a-(83/256:ℝ)) /
      (281474976710656:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf70).denominator a
    simp only [SourceBasis.rf70]
    nlinarith [hh]
  · norm_num [BasisData.rf70,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf71_translation (a : ℝ) :
    (BasisData.rf71).eval (a-83/256)=(SourceBasis.rf71).eval a := by
  apply translated_rf_of_scaled (BasisData.rf71) (SourceBasis.rf71) (1:ℝ) (1:ℝ) a (83/256)
  · have hh := RFChecks.e71n.sound RFChecks.e71n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e71n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e71n.left 0)=integerCoefficients (BasisData.rf71).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e71n.target0=affineShift (SourceBasis.rf71).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf71).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(65536:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf71).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(256:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(65536:ℤ)] (a-(83/256:ℝ))=(65536:ℝ) by simp [evalZ,horner]),(show evalZ [(256:ℤ)] (a-(83/256:ℝ))=(256:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf71] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf71).numerator.denominator = 256 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf71).numerator) (a-(83/256:ℝ)) /
      (256:ℝ) = (1:ℝ)*evalZ (SourceBasis.rf71).numerator a
    simp only [SourceBasis.rf71]
    nlinarith [hh]
  · have hh := RFChecks.e71d.sound RFChecks.e71d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e71d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e71d.left 0)=factorCoefficients (BasisData.rf71).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e71d.target0=affineShift (SourceBasis.rf71).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf71).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(256:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf71).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(256:ℤ)] (a-(83/256:ℝ))=(256:ℝ) by simp [evalZ,horner]),(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf71] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf71).factors = 1 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf71).factors) (a-(83/256:ℝ)) /
      (1:ℝ) = (1:ℝ)*evalZ (SourceBasis.rf71).denominator a
    simp only [SourceBasis.rf71]
    nlinarith [hh]
  · norm_num [BasisData.rf71,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf72_translation (a : ℝ) :
    (BasisData.rf72).eval (a-83/256)=(SourceBasis.rf72).eval a := by
  apply translated_rf_of_scaled (BasisData.rf72) (SourceBasis.rf72) (1/40:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e72n.sound RFChecks.e72n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e72n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e72n.left 0)=integerCoefficients (BasisData.rf72).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e72n.target0=affineShift (SourceBasis.rf72).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf72).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2882303761517117440:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf72).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(2814749767106560:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2882303761517117440:ℤ)] (a-(83/256:ℝ))=(2882303761517117440:ℝ) by simp [evalZ,horner]),(show evalZ [(2814749767106560:ℤ)] (a-(83/256:ℝ))=(2814749767106560:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf72] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf72).numerator.denominator = 2814749767106560 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf72).numerator) (a-(83/256:ℝ)) /
      (2814749767106560:ℝ) = (1/40:ℝ)*evalZ (SourceBasis.rf72).numerator a
    simp only [SourceBasis.rf72]
    nlinarith [hh]
  · have hh := RFChecks.e72d.sound RFChecks.e72d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e72d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e72d.left 0)=factorCoefficients (BasisData.rf72).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e72d.target0=affineShift (SourceBasis.rf72).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf72).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(8796093022208:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf72).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(8796093022208:ℤ)] (a-(83/256:ℝ))=(8796093022208:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf72] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf72).factors = 4294967296 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf72).factors) (a-(83/256:ℝ)) /
      (4294967296:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf72).denominator a
    simp only [SourceBasis.rf72]
    nlinarith [hh]
  · norm_num [BasisData.rf72,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf73_translation (a : ℝ) :
    (BasisData.rf73).eval (a-83/256)=(SourceBasis.rf73).eval a := by
  apply translated_rf_of_scaled (BasisData.rf73) (SourceBasis.rf73) (1/40:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e73n.sound RFChecks.e73n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e73n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e73n.left 0)=integerCoefficients (BasisData.rf73).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e73n.target0=affineShift (SourceBasis.rf73).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf73).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(737869762948382064640:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf73).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(360287970189639680:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(737869762948382064640:ℤ)] (a-(83/256:ℝ))=(737869762948382064640:ℝ) by simp [evalZ,horner]),(show evalZ [(360287970189639680:ℤ)] (a-(83/256:ℝ))=(360287970189639680:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf73] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf73).numerator.denominator = 360287970189639680 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf73).numerator) (a-(83/256:ℝ)) /
      (360287970189639680:ℝ) = (1/40:ℝ)*evalZ (SourceBasis.rf73).numerator a
    simp only [SourceBasis.rf73]
    nlinarith [hh]
  · have hh := RFChecks.e73d.sound RFChecks.e73d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e73d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e73d.left 0)=factorCoefficients (BasisData.rf73).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e73d.target0=affineShift (SourceBasis.rf73).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf73).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(8796093022208:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf73).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(8796093022208:ℤ)] (a-(83/256:ℝ))=(8796093022208:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf73] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf73).factors = 4294967296 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf73).factors) (a-(83/256:ℝ)) /
      (4294967296:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf73).denominator a
    simp only [SourceBasis.rf73]
    nlinarith [hh]
  · norm_num [BasisData.rf73,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf74_translation (a : ℝ) :
    (BasisData.rf74).eval (a-83/256)=(SourceBasis.rf74).eval a := by
  apply translated_rf_of_scaled (BasisData.rf74) (SourceBasis.rf74) (1/40:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e74n.sound RFChecks.e74n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e74n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e74n.left 0)=integerCoefficients (BasisData.rf74).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e74n.target0=affineShift (SourceBasis.rf74).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf74).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2882303761517117440:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf74).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(2814749767106560:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2882303761517117440:ℤ)] (a-(83/256:ℝ))=(2882303761517117440:ℝ) by simp [evalZ,horner]),(show evalZ [(2814749767106560:ℤ)] (a-(83/256:ℝ))=(2814749767106560:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf74] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf74).numerator.denominator = 2814749767106560 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf74).numerator) (a-(83/256:ℝ)) /
      (2814749767106560:ℝ) = (1/40:ℝ)*evalZ (SourceBasis.rf74).numerator a
    simp only [SourceBasis.rf74]
    nlinarith [hh]
  · have hh := RFChecks.e74d.sound RFChecks.e74d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e74d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e74d.left 0)=factorCoefficients (BasisData.rf74).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e74d.target0=affineShift (SourceBasis.rf74).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf74).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(8796093022208:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf74).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(8796093022208:ℤ)] (a-(83/256:ℝ))=(8796093022208:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf74] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf74).factors = 4294967296 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf74).factors) (a-(83/256:ℝ)) /
      (4294967296:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf74).denominator a
    simp only [SourceBasis.rf74]
    nlinarith [hh]
  · norm_num [BasisData.rf74,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf75_translation (a : ℝ) :
    (BasisData.rf75).eval (a-83/256)=(SourceBasis.rf75).eval a := by
  apply translated_rf_of_scaled (BasisData.rf75) (SourceBasis.rf75) (1/80:ℝ) (1/16:ℝ) a (83/256)
  · have hh := RFChecks.e75n.sound RFChecks.e75n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e75n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e75n.left 0)=integerCoefficients (BasisData.rf75).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e75n.target0=affineShift (SourceBasis.rf75).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf75).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(377789318629571617095680:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf75).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(368934881474191032320:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(377789318629571617095680:ℤ)] (a-(83/256:ℝ))=(377789318629571617095680:ℝ) by simp [evalZ,horner]),(show evalZ [(368934881474191032320:ℤ)] (a-(83/256:ℝ))=(368934881474191032320:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf75] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf75).numerator.denominator = 368934881474191032320 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf75).numerator) (a-(83/256:ℝ)) /
      (368934881474191032320:ℝ) = (1/80:ℝ)*evalZ (SourceBasis.rf75).numerator a
    simp only [SourceBasis.rf75]
    nlinarith [hh]
  · have hh := RFChecks.e75d.sound RFChecks.e75d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e75d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e75d.left 0)=factorCoefficients (BasisData.rf75).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e75d.target0=affineShift (SourceBasis.rf75).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf75).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(17592186044416:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf75).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(17592186044416:ℤ)] (a-(83/256:ℝ))=(17592186044416:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf75] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf75).factors = 4294967296 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf75).factors) (a-(83/256:ℝ)) /
      (4294967296:ℝ) = (1/16:ℝ)*evalZ (SourceBasis.rf75).denominator a
    simp only [SourceBasis.rf75]
    nlinarith [hh]
  · norm_num [BasisData.rf75,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf76_translation (a : ℝ) :
    (BasisData.rf76).eval (a-83/256)=(SourceBasis.rf76).eval a := by
  apply translated_rf_of_scaled (BasisData.rf76) (SourceBasis.rf76) (1/40:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e76n.sound RFChecks.e76n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e76n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e76n.left 0)=integerCoefficients (BasisData.rf76).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e76n.target0=affineShift (SourceBasis.rf76).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf76).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(737869762948382064640:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf76).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(360287970189639680:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(737869762948382064640:ℤ)] (a-(83/256:ℝ))=(737869762948382064640:ℝ) by simp [evalZ,horner]),(show evalZ [(360287970189639680:ℤ)] (a-(83/256:ℝ))=(360287970189639680:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf76] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf76).numerator.denominator = 360287970189639680 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf76).numerator) (a-(83/256:ℝ)) /
      (360287970189639680:ℝ) = (1/40:ℝ)*evalZ (SourceBasis.rf76).numerator a
    simp only [SourceBasis.rf76]
    nlinarith [hh]
  · have hh := RFChecks.e76d.sound RFChecks.e76d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e76d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e76d.left 0)=factorCoefficients (BasisData.rf76).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e76d.target0=affineShift (SourceBasis.rf76).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf76).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(8796093022208:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf76).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(8796093022208:ℤ)] (a-(83/256:ℝ))=(8796093022208:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf76] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf76).factors = 4294967296 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf76).factors) (a-(83/256:ℝ)) /
      (4294967296:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf76).denominator a
    simp only [SourceBasis.rf76]
    nlinarith [hh]
  · norm_num [BasisData.rf76,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf77_translation (a : ℝ) :
    (BasisData.rf77).eval (a-83/256)=(SourceBasis.rf77).eval a := by
  apply translated_rf_of_scaled (BasisData.rf77) (SourceBasis.rf77) (1/40:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e77n.sound RFChecks.e77n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e77n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e77n.left 0)=integerCoefficients (BasisData.rf77).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e77n.target0=affineShift (SourceBasis.rf77).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf77).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(737869762948382064640:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf77).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(360287970189639680:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(737869762948382064640:ℤ)] (a-(83/256:ℝ))=(737869762948382064640:ℝ) by simp [evalZ,horner]),(show evalZ [(360287970189639680:ℤ)] (a-(83/256:ℝ))=(360287970189639680:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf77] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf77).numerator.denominator = 360287970189639680 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf77).numerator) (a-(83/256:ℝ)) /
      (360287970189639680:ℝ) = (1/40:ℝ)*evalZ (SourceBasis.rf77).numerator a
    simp only [SourceBasis.rf77]
    nlinarith [hh]
  · have hh := RFChecks.e77d.sound RFChecks.e77d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e77d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e77d.left 0)=factorCoefficients (BasisData.rf77).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e77d.target0=affineShift (SourceBasis.rf77).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf77).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(8796093022208:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf77).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(8796093022208:ℤ)] (a-(83/256:ℝ))=(8796093022208:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf77] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf77).factors = 4294967296 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf77).factors) (a-(83/256:ℝ)) /
      (4294967296:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf77).denominator a
    simp only [SourceBasis.rf77]
    nlinarith [hh]
  · norm_num [BasisData.rf77,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf78_translation (a : ℝ) :
    (BasisData.rf78).eval (a-83/256)=(SourceBasis.rf78).eval a := by
  apply translated_rf_of_scaled (BasisData.rf78) (SourceBasis.rf78) (1:ℝ) (1:ℝ) a (83/256)
  · have hh := RFChecks.e78n.sound RFChecks.e78n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e78n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e78n.left 0)=integerCoefficients (BasisData.rf78).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e78n.target0=affineShift (SourceBasis.rf78).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf78).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf78).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(2147483648:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),(show evalZ [(2147483648:ℤ)] (a-(83/256:ℝ))=(2147483648:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf78] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf78).numerator.denominator = 2147483648 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf78).numerator) (a-(83/256:ℝ)) /
      (2147483648:ℝ) = (1:ℝ)*evalZ (SourceBasis.rf78).numerator a
    simp only [SourceBasis.rf78]
    nlinarith [hh]
  · have hh := RFChecks.e78d.sound RFChecks.e78d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e78d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e78d.left 0)=factorCoefficients (BasisData.rf78).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e78d.target0=affineShift (SourceBasis.rf78).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf78).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(65536:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf78).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(256:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(65536:ℤ)] (a-(83/256:ℝ))=(65536:ℝ) by simp [evalZ,horner]),(show evalZ [(256:ℤ)] (a-(83/256:ℝ))=(256:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf78] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf78).factors = 256 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf78).factors) (a-(83/256:ℝ)) /
      (256:ℝ) = (1:ℝ)*evalZ (SourceBasis.rf78).denominator a
    simp only [SourceBasis.rf78]
    nlinarith [hh]
  · norm_num [BasisData.rf78,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf79_translation (a : ℝ) :
    (BasisData.rf79).eval (a-83/256)=(SourceBasis.rf79).eval a := by
  apply translated_rf_of_scaled (BasisData.rf79) (SourceBasis.rf79) (1/120:ℝ) (1/24:ℝ) a (83/256)
  · have hh := RFChecks.e79n.sound RFChecks.e79n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e79n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e79n.left 0)=integerCoefficients (BasisData.rf79).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e79n.target0=affineShift (SourceBasis.rf79).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf79).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(8646911284551352320:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf79).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(33776997205278720:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(8646911284551352320:ℤ)] (a-(83/256:ℝ))=(8646911284551352320:ℝ) by simp [evalZ,horner]),(show evalZ [(33776997205278720:ℤ)] (a-(83/256:ℝ))=(33776997205278720:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf79] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf79).numerator.denominator = 33776997205278720 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf79).numerator) (a-(83/256:ℝ)) /
      (33776997205278720:ℝ) = (1/120:ℝ)*evalZ (SourceBasis.rf79).numerator a
    simp only [SourceBasis.rf79]
    nlinarith [hh]
  · have hh := RFChecks.e79d.sound RFChecks.e79d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e79d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e79d.left 0)=factorCoefficients (BasisData.rf79).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e79d.target0=affineShift (SourceBasis.rf79).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf79).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(26388279066624:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf79).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(26388279066624:ℤ)] (a-(83/256:ℝ))=(26388279066624:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf79] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf79).factors = 4294967296 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf79).factors) (a-(83/256:ℝ)) /
      (4294967296:ℝ) = (1/24:ℝ)*evalZ (SourceBasis.rf79).denominator a
    simp only [SourceBasis.rf79]
    nlinarith [hh]
  · norm_num [BasisData.rf79,ThomsonNegative.Compact.Packed.qval]
  · norm_num

#print axioms rf70_translation
end ThomsonNegative.Certificate.Bridges
