import ThomsonNegative.Certificate.Bridges.RFChecks01
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
theorem rf10_translation (a : ℝ) :
    (BasisData.rf10).eval (a-83/256)=(SourceBasis.rf10).eval a := by
  apply translated_rf_of_scaled (BasisData.rf10) (SourceBasis.rf10) (1/35:ℝ) (1:ℝ) a (83/256)
  · have hh := RFChecks.e10n.sound RFChecks.e10n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e10n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e10n.left 0)=integerCoefficients (BasisData.rf10).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e10n.target0=affineShift (SourceBasis.rf10).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf10).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(38482906972160:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf10).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(150323855360:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(38482906972160:ℤ)] (a-(83/256:ℝ))=(38482906972160:ℝ) by simp [evalZ,horner]),(show evalZ [(150323855360:ℤ)] (a-(83/256:ℝ))=(150323855360:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf10] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf10).numerator.denominator = 150323855360 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf10).numerator) (a-(83/256:ℝ)) /
      (150323855360:ℝ) = (1/35:ℝ)*evalZ (SourceBasis.rf10).numerator a
    simp only [SourceBasis.rf10]
    nlinarith [hh]
  · have hh := RFChecks.e10d.sound RFChecks.e10d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e10d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e10d.left 0)=factorCoefficients (BasisData.rf10).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e10d.target0=affineShift (SourceBasis.rf10).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf10).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(4294967296:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf10).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(16777216:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),(show evalZ [(16777216:ℤ)] (a-(83/256:ℝ))=(16777216:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf10] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf10).factors = 16777216 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf10).factors) (a-(83/256:ℝ)) /
      (16777216:ℝ) = (1:ℝ)*evalZ (SourceBasis.rf10).denominator a
    simp only [SourceBasis.rf10]
    nlinarith [hh]
  · norm_num [BasisData.rf10,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf11_translation (a : ℝ) :
    (BasisData.rf11).eval (a-83/256)=(SourceBasis.rf11).eval a := by
  apply translated_rf_of_scaled (BasisData.rf11) (SourceBasis.rf11) (1/70:ℝ) (1/2:ℝ) a (83/256)
  · have hh := RFChecks.e11n.sound RFChecks.e11n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e11n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e11n.left 0)=integerCoefficients (BasisData.rf11).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e11n.target0=affineShift (SourceBasis.rf11).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf11).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(19703248369745920:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf11).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(76965813944320:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(19703248369745920:ℤ)] (a-(83/256:ℝ))=(19703248369745920:ℝ) by simp [evalZ,horner]),(show evalZ [(76965813944320:ℤ)] (a-(83/256:ℝ))=(76965813944320:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf11] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf11).numerator.denominator = 76965813944320 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf11).numerator) (a-(83/256:ℝ)) /
      (76965813944320:ℝ) = (1/70:ℝ)*evalZ (SourceBasis.rf11).numerator a
    simp only [SourceBasis.rf11]
    nlinarith [hh]
  · have hh := RFChecks.e11d.sound RFChecks.e11d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e11d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e11d.left 0)=factorCoefficients (BasisData.rf11).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e11d.target0=affineShift (SourceBasis.rf11).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf11).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(8589934592:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf11).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(16777216:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(8589934592:ℤ)] (a-(83/256:ℝ))=(8589934592:ℝ) by simp [evalZ,horner]),(show evalZ [(16777216:ℤ)] (a-(83/256:ℝ))=(16777216:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf11] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf11).factors = 16777216 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf11).factors) (a-(83/256:ℝ)) /
      (16777216:ℝ) = (1/2:ℝ)*evalZ (SourceBasis.rf11).denominator a
    simp only [SourceBasis.rf11]
    nlinarith [hh]
  · norm_num [BasisData.rf11,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf12_translation (a : ℝ) :
    (BasisData.rf12).eval (a-83/256)=(SourceBasis.rf12).eval a := by
  apply translated_rf_of_scaled (BasisData.rf12) (SourceBasis.rf12) (1/35:ℝ) (1:ℝ) a (83/256)
  · have hh := RFChecks.e12n.sound RFChecks.e12n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e12n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e12n.left 0)=integerCoefficients (BasisData.rf12).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e12n.target0=affineShift (SourceBasis.rf12).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf12).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(150323855360:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf12).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(587202560:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(150323855360:ℤ)] (a-(83/256:ℝ))=(150323855360:ℝ) by simp [evalZ,horner]),(show evalZ [(587202560:ℤ)] (a-(83/256:ℝ))=(587202560:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf12] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf12).numerator.denominator = 587202560 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf12).numerator) (a-(83/256:ℝ)) /
      (587202560:ℝ) = (1/35:ℝ)*evalZ (SourceBasis.rf12).numerator a
    simp only [SourceBasis.rf12]
    nlinarith [hh]
  · have hh := RFChecks.e12d.sound RFChecks.e12d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e12d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e12d.left 0)=factorCoefficients (BasisData.rf12).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e12d.target0=affineShift (SourceBasis.rf12).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf12).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(16777216:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf12).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(65536:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(16777216:ℤ)] (a-(83/256:ℝ))=(16777216:ℝ) by simp [evalZ,horner]),(show evalZ [(65536:ℤ)] (a-(83/256:ℝ))=(65536:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf12] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf12).factors = 65536 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf12).factors) (a-(83/256:ℝ)) /
      (65536:ℝ) = (1:ℝ)*evalZ (SourceBasis.rf12).denominator a
    simp only [SourceBasis.rf12]
    nlinarith [hh]
  · norm_num [BasisData.rf12,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf13_translation (a : ℝ) :
    (BasisData.rf13).eval (a-83/256)=(SourceBasis.rf13).eval a := by
  apply translated_rf_of_scaled (BasisData.rf13) (SourceBasis.rf13) (1/70:ℝ) (1/2:ℝ) a (83/256)
  · have hh := RFChecks.e13n.sound RFChecks.e13n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e13n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e13n.left 0)=integerCoefficients (BasisData.rf13).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e13n.target0=affineShift (SourceBasis.rf13).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf13).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(76965813944320:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf13).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(300647710720:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(76965813944320:ℤ)] (a-(83/256:ℝ))=(76965813944320:ℝ) by simp [evalZ,horner]),(show evalZ [(300647710720:ℤ)] (a-(83/256:ℝ))=(300647710720:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf13] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf13).numerator.denominator = 300647710720 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf13).numerator) (a-(83/256:ℝ)) /
      (300647710720:ℝ) = (1/70:ℝ)*evalZ (SourceBasis.rf13).numerator a
    simp only [SourceBasis.rf13]
    nlinarith [hh]
  · have hh := RFChecks.e13d.sound RFChecks.e13d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e13d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e13d.left 0)=factorCoefficients (BasisData.rf13).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e13d.target0=affineShift (SourceBasis.rf13).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf13).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(33554432:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf13).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(65536:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(33554432:ℤ)] (a-(83/256:ℝ))=(33554432:ℝ) by simp [evalZ,horner]),(show evalZ [(65536:ℤ)] (a-(83/256:ℝ))=(65536:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf13] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf13).factors = 65536 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf13).factors) (a-(83/256:ℝ)) /
      (65536:ℝ) = (1/2:ℝ)*evalZ (SourceBasis.rf13).denominator a
    simp only [SourceBasis.rf13]
    nlinarith [hh]
  · norm_num [BasisData.rf13,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf14_translation (a : ℝ) :
    (BasisData.rf14).eval (a-83/256)=(SourceBasis.rf14).eval a := by
  apply translated_rf_of_scaled (BasisData.rf14) (SourceBasis.rf14) (1/35:ℝ) (1:ℝ) a (83/256)
  · have hh := RFChecks.e14n.sound RFChecks.e14n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e14n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e14n.left 0)=integerCoefficients (BasisData.rf14).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e14n.target0=affineShift (SourceBasis.rf14).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf14).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(150323855360:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf14).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(587202560:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(150323855360:ℤ)] (a-(83/256:ℝ))=(150323855360:ℝ) by simp [evalZ,horner]),(show evalZ [(587202560:ℤ)] (a-(83/256:ℝ))=(587202560:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf14] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf14).numerator.denominator = 587202560 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf14).numerator) (a-(83/256:ℝ)) /
      (587202560:ℝ) = (1/35:ℝ)*evalZ (SourceBasis.rf14).numerator a
    simp only [SourceBasis.rf14]
    nlinarith [hh]
  · have hh := RFChecks.e14d.sound RFChecks.e14d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e14d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e14d.left 0)=factorCoefficients (BasisData.rf14).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e14d.target0=affineShift (SourceBasis.rf14).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf14).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(16777216:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf14).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(65536:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(16777216:ℤ)] (a-(83/256:ℝ))=(16777216:ℝ) by simp [evalZ,horner]),(show evalZ [(65536:ℤ)] (a-(83/256:ℝ))=(65536:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf14] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf14).factors = 65536 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf14).factors) (a-(83/256:ℝ)) /
      (65536:ℝ) = (1:ℝ)*evalZ (SourceBasis.rf14).denominator a
    simp only [SourceBasis.rf14]
    nlinarith [hh]
  · norm_num [BasisData.rf14,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf15_translation (a : ℝ) :
    (BasisData.rf15).eval (a-83/256)=(SourceBasis.rf15).eval a := by
  apply translated_rf_of_scaled (BasisData.rf15) (SourceBasis.rf15) (1/70:ℝ) (1/2:ℝ) a (83/256)
  · have hh := RFChecks.e15n.sound RFChecks.e15n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e15n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e15n.left 0)=integerCoefficients (BasisData.rf15).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e15n.target0=affineShift (SourceBasis.rf15).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf15).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(76965813944320:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf15).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(300647710720:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(76965813944320:ℤ)] (a-(83/256:ℝ))=(76965813944320:ℝ) by simp [evalZ,horner]),(show evalZ [(300647710720:ℤ)] (a-(83/256:ℝ))=(300647710720:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf15] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf15).numerator.denominator = 300647710720 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf15).numerator) (a-(83/256:ℝ)) /
      (300647710720:ℝ) = (1/70:ℝ)*evalZ (SourceBasis.rf15).numerator a
    simp only [SourceBasis.rf15]
    nlinarith [hh]
  · have hh := RFChecks.e15d.sound RFChecks.e15d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e15d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e15d.left 0)=factorCoefficients (BasisData.rf15).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e15d.target0=affineShift (SourceBasis.rf15).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf15).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(33554432:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf15).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(65536:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(33554432:ℤ)] (a-(83/256:ℝ))=(33554432:ℝ) by simp [evalZ,horner]),(show evalZ [(65536:ℤ)] (a-(83/256:ℝ))=(65536:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf15] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf15).factors = 65536 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf15).factors) (a-(83/256:ℝ)) /
      (65536:ℝ) = (1/2:ℝ)*evalZ (SourceBasis.rf15).denominator a
    simp only [SourceBasis.rf15]
    nlinarith [hh]
  · norm_num [BasisData.rf15,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf16_translation (a : ℝ) :
    (BasisData.rf16).eval (a-83/256)=(SourceBasis.rf16).eval a := by
  apply translated_rf_of_scaled (BasisData.rf16) (SourceBasis.rf16) (1/10:ℝ) (1/10:ℝ) a (83/256)
  · have hh := RFChecks.e16n.sound RFChecks.e16n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e16n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e16n.left 0)=integerCoefficients (BasisData.rf16).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e16n.target0=affineShift (SourceBasis.rf16).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf16).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(42949672960:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf16).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(167772160:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(42949672960:ℤ)] (a-(83/256:ℝ))=(42949672960:ℝ) by simp [evalZ,horner]),(show evalZ [(167772160:ℤ)] (a-(83/256:ℝ))=(167772160:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf16] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf16).numerator.denominator = 167772160 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf16).numerator) (a-(83/256:ℝ)) /
      (167772160:ℝ) = (1/10:ℝ)*evalZ (SourceBasis.rf16).numerator a
    simp only [SourceBasis.rf16]
    nlinarith [hh]
  · have hh := RFChecks.e16d.sound RFChecks.e16d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e16d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e16d.left 0)=factorCoefficients (BasisData.rf16).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e16d.target0=affineShift (SourceBasis.rf16).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf16).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(167772160:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf16).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(65536:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(167772160:ℤ)] (a-(83/256:ℝ))=(167772160:ℝ) by simp [evalZ,horner]),(show evalZ [(65536:ℤ)] (a-(83/256:ℝ))=(65536:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf16] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf16).factors = 65536 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf16).factors) (a-(83/256:ℝ)) /
      (65536:ℝ) = (1/10:ℝ)*evalZ (SourceBasis.rf16).denominator a
    simp only [SourceBasis.rf16]
    nlinarith [hh]
  · norm_num [BasisData.rf16,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf17_translation (a : ℝ) :
    (BasisData.rf17).eval (a-83/256)=(SourceBasis.rf17).eval a := by
  apply translated_rf_of_scaled (BasisData.rf17) (SourceBasis.rf17) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e17n.sound RFChecks.e17n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e17n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e17n.left 0)=integerCoefficients (BasisData.rf17).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e17n.target0=affineShift (SourceBasis.rf17).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf17).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(16971004547812787486720:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf17).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(16573246628723425280:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(16971004547812787486720:ℤ)] (a-(83/256:ℝ))=(16971004547812787486720:ℝ) by simp [evalZ,horner]),(show evalZ [(16573246628723425280:ℤ)] (a-(83/256:ℝ))=(16573246628723425280:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf17] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf17).numerator.denominator = 16573246628723425280 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf17).numerator) (a-(83/256:ℝ)) /
      (16573246628723425280:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf17).numerator a
    simp only [SourceBasis.rf17]
    nlinarith [hh]
  · have hh := RFChecks.e17d.sound RFChecks.e17d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e17d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e17d.left 0)=factorCoefficients (BasisData.rf17).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e17d.target0=affineShift (SourceBasis.rf17).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf17).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf17).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ))=(2251799813685248:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf17] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf17).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf17).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf17).denominator a
    simp only [SourceBasis.rf17]
    nlinarith [hh]
  · norm_num [BasisData.rf17,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf18_translation (a : ℝ) :
    (BasisData.rf18).eval (a-83/256)=(SourceBasis.rf18).eval a := by
  apply translated_rf_of_scaled (BasisData.rf18) (SourceBasis.rf18) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e18n.sound RFChecks.e18n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e18n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e18n.left 0)=integerCoefficients (BasisData.rf18).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e18n.target0=affineShift (SourceBasis.rf18).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf18).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(4344577164240073596600320:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf18).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(2121375568476598435840:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(4344577164240073596600320:ℤ)] (a-(83/256:ℝ))=(4344577164240073596600320:ℝ) by simp [evalZ,horner]),(show evalZ [(2121375568476598435840:ℤ)] (a-(83/256:ℝ))=(2121375568476598435840:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf18] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf18).numerator.denominator = 2121375568476598435840 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf18).numerator) (a-(83/256:ℝ)) /
      (2121375568476598435840:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf18).numerator a
    simp only [SourceBasis.rf18]
    nlinarith [hh]
  · have hh := RFChecks.e18d.sound RFChecks.e18d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e18d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e18d.left 0)=factorCoefficients (BasisData.rf18).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e18d.target0=affineShift (SourceBasis.rf18).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf18).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf18).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ))=(2251799813685248:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf18] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf18).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf18).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf18).denominator a
    simp only [SourceBasis.rf18]
    nlinarith [hh]
  · norm_num [BasisData.rf18,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf19_translation (a : ℝ) :
    (BasisData.rf19).eval (a-83/256)=(SourceBasis.rf19).eval a := by
  apply translated_rf_of_scaled (BasisData.rf19) (SourceBasis.rf19) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e19n.sound RFChecks.e19n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e19n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e19n.left 0)=integerCoefficients (BasisData.rf19).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e19n.target0=affineShift (SourceBasis.rf19).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf19).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(16971004547812787486720:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf19).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(16573246628723425280:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(16971004547812787486720:ℤ)] (a-(83/256:ℝ))=(16971004547812787486720:ℝ) by simp [evalZ,horner]),(show evalZ [(16573246628723425280:ℤ)] (a-(83/256:ℝ))=(16573246628723425280:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf19] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf19).numerator.denominator = 16573246628723425280 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf19).numerator) (a-(83/256:ℝ)) /
      (16573246628723425280:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf19).numerator a
    simp only [SourceBasis.rf19]
    nlinarith [hh]
  · have hh := RFChecks.e19d.sound RFChecks.e19d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e19d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e19d.left 0)=factorCoefficients (BasisData.rf19).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e19d.target0=affineShift (SourceBasis.rf19).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf19).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf19).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ))=(2251799813685248:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf19] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf19).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf19).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf19).denominator a
    simp only [SourceBasis.rf19]
    nlinarith [hh]
  · norm_num [BasisData.rf19,ThomsonNegative.Compact.Packed.qval]
  · norm_num

#print axioms rf10_translation
end ThomsonNegative.Certificate.Bridges
