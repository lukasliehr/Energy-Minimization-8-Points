import ThomsonNegative.Certificate.Bridges.RFChecks00
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
theorem rf0_translation (a : ℝ) :
    (BasisData.rf0).eval (a-83/256)=(SourceBasis.rf0).eval a := by
  apply translated_rf_of_scaled (BasisData.rf0) (SourceBasis.rf0) (1:ℝ) (1:ℝ) a (83/256)
  · have hh := RFChecks.e0n.sound RFChecks.e0n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e0n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e0n.left 0)=integerCoefficients (BasisData.rf0).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e0n.target0=affineShift (SourceBasis.rf0).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf0).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf0).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(1:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf0] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf0).numerator.denominator = 1 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf0).numerator) (a-(83/256:ℝ)) /
      (1:ℝ) = (1:ℝ)*evalZ (SourceBasis.rf0).numerator a
    simp only [SourceBasis.rf0]
    nlinarith [hh]
  · have hh := RFChecks.e0d.sound RFChecks.e0d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e0d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e0d.left 0)=factorCoefficients (BasisData.rf0).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e0d.target0=affineShift (SourceBasis.rf0).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf0).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(256:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf0).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(256:ℤ)] (a-(83/256:ℝ))=(256:ℝ) by simp [evalZ,horner]),(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf0] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf0).factors = 1 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf0).factors) (a-(83/256:ℝ)) /
      (1:ℝ) = (1:ℝ)*evalZ (SourceBasis.rf0).denominator a
    simp only [SourceBasis.rf0]
    nlinarith [hh]
  · norm_num [BasisData.rf0,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf1_translation (a : ℝ) :
    (BasisData.rf1).eval (a-83/256)=(SourceBasis.rf1).eval a := by
  apply translated_rf_of_scaled (BasisData.rf1) (SourceBasis.rf1) (1/2:ℝ) (1/2:ℝ) a (83/256)
  · have hh := RFChecks.e1n.sound RFChecks.e1n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e1n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e1n.left 0)=integerCoefficients (BasisData.rf1).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e1n.target0=affineShift (SourceBasis.rf1).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf1).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(33554432:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf1).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(131072:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(33554432:ℤ)] (a-(83/256:ℝ))=(33554432:ℝ) by simp [evalZ,horner]),(show evalZ [(131072:ℤ)] (a-(83/256:ℝ))=(131072:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf1] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf1).numerator.denominator = 131072 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf1).numerator) (a-(83/256:ℝ)) /
      (131072:ℝ) = (1/2:ℝ)*evalZ (SourceBasis.rf1).numerator a
    simp only [SourceBasis.rf1]
    nlinarith [hh]
  · have hh := RFChecks.e1d.sound RFChecks.e1d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e1d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e1d.left 0)=factorCoefficients (BasisData.rf1).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e1d.target0=affineShift (SourceBasis.rf1).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf1).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(512:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf1).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(512:ℤ)] (a-(83/256:ℝ))=(512:ℝ) by simp [evalZ,horner]),(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf1] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf1).factors = 1 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf1).factors) (a-(83/256:ℝ)) /
      (1:ℝ) = (1/2:ℝ)*evalZ (SourceBasis.rf1).denominator a
    simp only [SourceBasis.rf1]
    nlinarith [hh]
  · norm_num [BasisData.rf1,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf2_translation (a : ℝ) :
    (BasisData.rf2).eval (a-83/256)=(SourceBasis.rf2).eval a := by
  apply translated_rf_of_scaled (BasisData.rf2) (SourceBasis.rf2) (1/8:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e2n.sound RFChecks.e2n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e2n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e2n.left 0)=integerCoefficients (BasisData.rf2).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e2n.target0=affineShift (SourceBasis.rf2).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf2).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(8796093022208:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf2).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(34359738368:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(8796093022208:ℤ)] (a-(83/256:ℝ))=(8796093022208:ℝ) by simp [evalZ,horner]),(show evalZ [(34359738368:ℤ)] (a-(83/256:ℝ))=(34359738368:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf2] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf2).numerator.denominator = 34359738368 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf2).numerator) (a-(83/256:ℝ)) /
      (34359738368:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf2).numerator a
    simp only [SourceBasis.rf2]
    nlinarith [hh]
  · have hh := RFChecks.e2d.sound RFChecks.e2d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e2d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e2d.left 0)=factorCoefficients (BasisData.rf2).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e2d.target0=affineShift (SourceBasis.rf2).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf2).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2048:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf2).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2048:ℤ)] (a-(83/256:ℝ))=(2048:ℝ) by simp [evalZ,horner]),(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf2] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf2).factors = 1 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf2).factors) (a-(83/256:ℝ)) /
      (1:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf2).denominator a
    simp only [SourceBasis.rf2]
    nlinarith [hh]
  · norm_num [BasisData.rf2,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf3_translation (a : ℝ) :
    (BasisData.rf3).eval (a-83/256)=(SourceBasis.rf3).eval a := by
  apply translated_rf_of_scaled (BasisData.rf3) (SourceBasis.rf3) (1/8:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e3n.sound RFChecks.e3n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e3n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e3n.left 0)=integerCoefficients (BasisData.rf3).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e3n.target0=affineShift (SourceBasis.rf3).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf3).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf3).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(8796093022208:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ))=(2251799813685248:ℝ) by simp [evalZ,horner]),(show evalZ [(8796093022208:ℤ)] (a-(83/256:ℝ))=(8796093022208:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf3] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf3).numerator.denominator = 8796093022208 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf3).numerator) (a-(83/256:ℝ)) /
      (8796093022208:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf3).numerator a
    simp only [SourceBasis.rf3]
    nlinarith [hh]
  · have hh := RFChecks.e3d.sound RFChecks.e3d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e3d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e3d.left 0)=factorCoefficients (BasisData.rf3).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e3d.target0=affineShift (SourceBasis.rf3).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf3).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2048:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf3).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2048:ℤ)] (a-(83/256:ℝ))=(2048:ℝ) by simp [evalZ,horner]),(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf3] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf3).factors = 1 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf3).factors) (a-(83/256:ℝ)) /
      (1:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf3).denominator a
    simp only [SourceBasis.rf3]
    nlinarith [hh]
  · norm_num [BasisData.rf3,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf4_translation (a : ℝ) :
    (BasisData.rf4).eval (a-83/256)=(SourceBasis.rf4).eval a := by
  apply translated_rf_of_scaled (BasisData.rf4) (SourceBasis.rf4) (1/16:ℝ) (1/16:ℝ) a (83/256)
  · have hh := RFChecks.e4n.sound RFChecks.e4n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e4n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e4n.left 0)=integerCoefficients (BasisData.rf4).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e4n.target0=affineShift (SourceBasis.rf4).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf4).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1152921504606846976:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf4).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(4503599627370496:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1152921504606846976:ℤ)] (a-(83/256:ℝ))=(1152921504606846976:ℝ) by simp [evalZ,horner]),(show evalZ [(4503599627370496:ℤ)] (a-(83/256:ℝ))=(4503599627370496:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf4] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf4).numerator.denominator = 4503599627370496 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf4).numerator) (a-(83/256:ℝ)) /
      (4503599627370496:ℝ) = (1/16:ℝ)*evalZ (SourceBasis.rf4).numerator a
    simp only [SourceBasis.rf4]
    nlinarith [hh]
  · have hh := RFChecks.e4d.sound RFChecks.e4d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e4d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e4d.left 0)=factorCoefficients (BasisData.rf4).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e4d.target0=affineShift (SourceBasis.rf4).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf4).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(4096:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf4).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(4096:ℤ)] (a-(83/256:ℝ))=(4096:ℝ) by simp [evalZ,horner]),(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf4] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf4).factors = 1 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf4).factors) (a-(83/256:ℝ)) /
      (1:ℝ) = (1/16:ℝ)*evalZ (SourceBasis.rf4).denominator a
    simp only [SourceBasis.rf4]
    nlinarith [hh]
  · norm_num [BasisData.rf4,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf5_translation (a : ℝ) :
    (BasisData.rf5).eval (a-83/256)=(SourceBasis.rf5).eval a := by
  apply translated_rf_of_scaled (BasisData.rf5) (SourceBasis.rf5) (1:ℝ) (1:ℝ) a (83/256)
  · have hh := RFChecks.e5n.sound RFChecks.e5n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e5n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e5n.left 0)=integerCoefficients (BasisData.rf5).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e5n.target0=affineShift (SourceBasis.rf5).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf5).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(256:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf5).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(1:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(256:ℤ)] (a-(83/256:ℝ))=(256:ℝ) by simp [evalZ,horner]),(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf5] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf5).numerator.denominator = 1 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf5).numerator) (a-(83/256:ℝ)) /
      (1:ℝ) = (1:ℝ)*evalZ (SourceBasis.rf5).numerator a
    simp only [SourceBasis.rf5]
    nlinarith [hh]
  · have hh := RFChecks.e5d.sound RFChecks.e5d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e5d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e5d.left 0)=factorCoefficients (BasisData.rf5).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e5d.target0=affineShift (SourceBasis.rf5).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf5).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(256:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf5).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(256:ℤ)] (a-(83/256:ℝ))=(256:ℝ) by simp [evalZ,horner]),(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf5] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf5).factors = 1 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf5).factors) (a-(83/256:ℝ)) /
      (1:ℝ) = (1:ℝ)*evalZ (SourceBasis.rf5).denominator a
    simp only [SourceBasis.rf5]
    nlinarith [hh]
  · norm_num [BasisData.rf5,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf6_translation (a : ℝ) :
    (BasisData.rf6).eval (a-83/256)=(SourceBasis.rf6).eval a := by
  apply translated_rf_of_scaled (BasisData.rf6) (SourceBasis.rf6) (1/35:ℝ) (1:ℝ) a (83/256)
  · have hh := RFChecks.e6n.sound RFChecks.e6n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e6n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e6n.left 0)=integerCoefficients (BasisData.rf6).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e6n.target0=affineShift (SourceBasis.rf6).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf6).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2293760:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf6).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(2240:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2293760:ℤ)] (a-(83/256:ℝ))=(2293760:ℝ) by simp [evalZ,horner]),(show evalZ [(2240:ℤ)] (a-(83/256:ℝ))=(2240:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf6] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf6).numerator.denominator = 2240 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf6).numerator) (a-(83/256:ℝ)) /
      (2240:ℝ) = (1/35:ℝ)*evalZ (SourceBasis.rf6).numerator a
    simp only [SourceBasis.rf6]
    nlinarith [hh]
  · have hh := RFChecks.e6d.sound RFChecks.e6d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e6d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e6d.left 0)=factorCoefficients (BasisData.rf6).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e6d.target0=affineShift (SourceBasis.rf6).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf6).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(4294967296:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf6).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(16777216:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),(show evalZ [(16777216:ℤ)] (a-(83/256:ℝ))=(16777216:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf6] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf6).factors = 16777216 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf6).factors) (a-(83/256:ℝ)) /
      (16777216:ℝ) = (1:ℝ)*evalZ (SourceBasis.rf6).denominator a
    simp only [SourceBasis.rf6]
    nlinarith [hh]
  · norm_num [BasisData.rf6,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf7_translation (a : ℝ) :
    (BasisData.rf7).eval (a-83/256)=(SourceBasis.rf7).eval a := by
  apply translated_rf_of_scaled (BasisData.rf7) (SourceBasis.rf7) (1/35:ℝ) (1:ℝ) a (83/256)
  · have hh := RFChecks.e7n.sound RFChecks.e7n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e7n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e7n.left 0)=integerCoefficients (BasisData.rf7).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e7n.target0=affineShift (SourceBasis.rf7).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf7).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(38482906972160:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf7).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(150323855360:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(38482906972160:ℤ)] (a-(83/256:ℝ))=(38482906972160:ℝ) by simp [evalZ,horner]),(show evalZ [(150323855360:ℤ)] (a-(83/256:ℝ))=(150323855360:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf7] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf7).numerator.denominator = 150323855360 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf7).numerator) (a-(83/256:ℝ)) /
      (150323855360:ℝ) = (1/35:ℝ)*evalZ (SourceBasis.rf7).numerator a
    simp only [SourceBasis.rf7]
    nlinarith [hh]
  · have hh := RFChecks.e7d.sound RFChecks.e7d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e7d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e7d.left 0)=factorCoefficients (BasisData.rf7).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e7d.target0=affineShift (SourceBasis.rf7).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf7).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(4294967296:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf7).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(16777216:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),(show evalZ [(16777216:ℤ)] (a-(83/256:ℝ))=(16777216:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf7] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf7).factors = 16777216 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf7).factors) (a-(83/256:ℝ)) /
      (16777216:ℝ) = (1:ℝ)*evalZ (SourceBasis.rf7).denominator a
    simp only [SourceBasis.rf7]
    nlinarith [hh]
  · norm_num [BasisData.rf7,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf8_translation (a : ℝ) :
    (BasisData.rf8).eval (a-83/256)=(SourceBasis.rf8).eval a := by
  apply translated_rf_of_scaled (BasisData.rf8) (SourceBasis.rf8) (1/70:ℝ) (1/2:ℝ) a (83/256)
  · have hh := RFChecks.e8n.sound RFChecks.e8n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e8n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e8n.left 0)=integerCoefficients (BasisData.rf8).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e8n.target0=affineShift (SourceBasis.rf8).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf8).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(19703248369745920:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf8).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(76965813944320:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(19703248369745920:ℤ)] (a-(83/256:ℝ))=(19703248369745920:ℝ) by simp [evalZ,horner]),(show evalZ [(76965813944320:ℤ)] (a-(83/256:ℝ))=(76965813944320:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf8] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf8).numerator.denominator = 76965813944320 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf8).numerator) (a-(83/256:ℝ)) /
      (76965813944320:ℝ) = (1/70:ℝ)*evalZ (SourceBasis.rf8).numerator a
    simp only [SourceBasis.rf8]
    nlinarith [hh]
  · have hh := RFChecks.e8d.sound RFChecks.e8d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e8d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e8d.left 0)=factorCoefficients (BasisData.rf8).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e8d.target0=affineShift (SourceBasis.rf8).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf8).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(8589934592:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf8).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(16777216:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(8589934592:ℤ)] (a-(83/256:ℝ))=(8589934592:ℝ) by simp [evalZ,horner]),(show evalZ [(16777216:ℤ)] (a-(83/256:ℝ))=(16777216:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf8] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf8).factors = 16777216 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf8).factors) (a-(83/256:ℝ)) /
      (16777216:ℝ) = (1/2:ℝ)*evalZ (SourceBasis.rf8).denominator a
    simp only [SourceBasis.rf8]
    nlinarith [hh]
  · norm_num [BasisData.rf8,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf9_translation (a : ℝ) :
    (BasisData.rf9).eval (a-83/256)=(SourceBasis.rf9).eval a := by
  apply translated_rf_of_scaled (BasisData.rf9) (SourceBasis.rf9) (1/35:ℝ) (1:ℝ) a (83/256)
  · have hh := RFChecks.e9n.sound RFChecks.e9n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e9n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e9n.left 0)=integerCoefficients (BasisData.rf9).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e9n.target0=affineShift (SourceBasis.rf9).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf9).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2293760:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf9).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(2240:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2293760:ℤ)] (a-(83/256:ℝ))=(2293760:ℝ) by simp [evalZ,horner]),(show evalZ [(2240:ℤ)] (a-(83/256:ℝ))=(2240:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf9] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf9).numerator.denominator = 2240 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf9).numerator) (a-(83/256:ℝ)) /
      (2240:ℝ) = (1/35:ℝ)*evalZ (SourceBasis.rf9).numerator a
    simp only [SourceBasis.rf9]
    nlinarith [hh]
  · have hh := RFChecks.e9d.sound RFChecks.e9d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e9d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e9d.left 0)=factorCoefficients (BasisData.rf9).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e9d.target0=affineShift (SourceBasis.rf9).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf9).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(4294967296:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf9).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(16777216:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),(show evalZ [(16777216:ℤ)] (a-(83/256:ℝ))=(16777216:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf9] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf9).factors = 16777216 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf9).factors) (a-(83/256:ℝ)) /
      (16777216:ℝ) = (1:ℝ)*evalZ (SourceBasis.rf9).denominator a
    simp only [SourceBasis.rf9]
    nlinarith [hh]
  · norm_num [BasisData.rf9,ThomsonNegative.Compact.Packed.qval]
  · norm_num

#print axioms rf0_translation
end ThomsonNegative.Certificate.Bridges
