import ThomsonNegative.Certificate.Bridges.RFChecks02
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
theorem rf20_translation (a : ℝ) :
    (BasisData.rf20).eval (a-83/256)=(SourceBasis.rf20).eval a := by
  apply translated_rf_of_scaled (BasisData.rf20) (SourceBasis.rf20) (1/1840:ℝ) (1/16:ℝ) a (83/256)
  · have hh := RFChecks.e20n.sound RFChecks.e20n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e20n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e20n.left 0)=integerCoefficients (BasisData.rf20).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e20n.target0=affineShift (SourceBasis.rf20).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf20).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2224423508090917681459363840:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf20).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(2172288582120036798300160:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2224423508090917681459363840:ℤ)] (a-(83/256:ℝ))=(2224423508090917681459363840:ℝ) by simp [evalZ,horner]),(show evalZ [(2172288582120036798300160:ℤ)] (a-(83/256:ℝ))=(2172288582120036798300160:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf20] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf20).numerator.denominator = 2172288582120036798300160 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf20).numerator) (a-(83/256:ℝ)) /
      (2172288582120036798300160:ℝ) = (1/1840:ℝ)*evalZ (SourceBasis.rf20).numerator a
    simp only [SourceBasis.rf20]
    nlinarith [hh]
  · have hh := RFChecks.e20d.sound RFChecks.e20d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e20d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e20d.left 0)=factorCoefficients (BasisData.rf20).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e20d.target0=affineShift (SourceBasis.rf20).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf20).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(4503599627370496:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf20).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(4503599627370496:ℤ)] (a-(83/256:ℝ))=(4503599627370496:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf20] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf20).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf20).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/16:ℝ)*evalZ (SourceBasis.rf20).denominator a
    simp only [SourceBasis.rf20]
    nlinarith [hh]
  · norm_num [BasisData.rf20,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf21_translation (a : ℝ) :
    (BasisData.rf21).eval (a-83/256)=(SourceBasis.rf21).eval a := by
  apply translated_rf_of_scaled (BasisData.rf21) (SourceBasis.rf21) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e21n.sound RFChecks.e21n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e21n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e21n.left 0)=integerCoefficients (BasisData.rf21).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e21n.target0=affineShift (SourceBasis.rf21).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf21).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(4344577164240073596600320:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf21).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(2121375568476598435840:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(4344577164240073596600320:ℤ)] (a-(83/256:ℝ))=(4344577164240073596600320:ℝ) by simp [evalZ,horner]),(show evalZ [(2121375568476598435840:ℤ)] (a-(83/256:ℝ))=(2121375568476598435840:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf21] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf21).numerator.denominator = 2121375568476598435840 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf21).numerator) (a-(83/256:ℝ)) /
      (2121375568476598435840:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf21).numerator a
    simp only [SourceBasis.rf21]
    nlinarith [hh]
  · have hh := RFChecks.e21d.sound RFChecks.e21d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e21d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e21d.left 0)=factorCoefficients (BasisData.rf21).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e21d.target0=affineShift (SourceBasis.rf21).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf21).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf21).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ))=(2251799813685248:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf21] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf21).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf21).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf21).denominator a
    simp only [SourceBasis.rf21]
    nlinarith [hh]
  · norm_num [BasisData.rf21,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf22_translation (a : ℝ) :
    (BasisData.rf22).eval (a-83/256)=(SourceBasis.rf22).eval a := by
  apply translated_rf_of_scaled (BasisData.rf22) (SourceBasis.rf22) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e22n.sound RFChecks.e22n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e22n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e22n.left 0)=integerCoefficients (BasisData.rf22).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e22n.target0=affineShift (SourceBasis.rf22).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf22).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(4344577164240073596600320:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf22).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(265171946059574804480:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(4344577164240073596600320:ℤ)] (a-(83/256:ℝ))=(4344577164240073596600320:ℝ) by simp [evalZ,horner]),(show evalZ [(265171946059574804480:ℤ)] (a-(83/256:ℝ))=(265171946059574804480:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf22] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf22).numerator.denominator = 265171946059574804480 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf22).numerator) (a-(83/256:ℝ)) /
      (265171946059574804480:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf22).numerator a
    simp only [SourceBasis.rf22]
    nlinarith [hh]
  · have hh := RFChecks.e22d.sound RFChecks.e22d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e22d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e22d.left 0)=factorCoefficients (BasisData.rf22).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e22d.target0=affineShift (SourceBasis.rf22).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf22).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf22).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ))=(2251799813685248:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf22] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf22).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf22).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf22).denominator a
    simp only [SourceBasis.rf22]
    nlinarith [hh]
  · norm_num [BasisData.rf22,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf23_translation (a : ℝ) :
    (BasisData.rf23).eval (a-83/256)=(SourceBasis.rf23).eval a := by
  apply translated_rf_of_scaled (BasisData.rf23) (SourceBasis.rf23) (1/1840:ℝ) (1/16:ℝ) a (83/256)
  · have hh := RFChecks.e23n.sound RFChecks.e23n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e23n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e23n.left 0)=integerCoefficients (BasisData.rf23).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e23n.target0=affineShift (SourceBasis.rf23).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf23).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(569452418071274926453597143040:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf23).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(278052938511364710182420480:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(569452418071274926453597143040:ℤ)] (a-(83/256:ℝ))=(569452418071274926453597143040:ℝ) by simp [evalZ,horner]),(show evalZ [(278052938511364710182420480:ℤ)] (a-(83/256:ℝ))=(278052938511364710182420480:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf23] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf23).numerator.denominator = 278052938511364710182420480 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf23).numerator) (a-(83/256:ℝ)) /
      (278052938511364710182420480:ℝ) = (1/1840:ℝ)*evalZ (SourceBasis.rf23).numerator a
    simp only [SourceBasis.rf23]
    nlinarith [hh]
  · have hh := RFChecks.e23d.sound RFChecks.e23d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e23d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e23d.left 0)=factorCoefficients (BasisData.rf23).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e23d.target0=affineShift (SourceBasis.rf23).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf23).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(4503599627370496:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf23).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(4503599627370496:ℤ)] (a-(83/256:ℝ))=(4503599627370496:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf23] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf23).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf23).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/16:ℝ)*evalZ (SourceBasis.rf23).denominator a
    simp only [SourceBasis.rf23]
    nlinarith [hh]
  · norm_num [BasisData.rf23,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf24_translation (a : ℝ) :
    (BasisData.rf24).eval (a-83/256)=(SourceBasis.rf24).eval a := by
  apply translated_rf_of_scaled (BasisData.rf24) (SourceBasis.rf24) (1/1840:ℝ) (1/16:ℝ) a (83/256)
  · have hh := RFChecks.e24n.sound RFChecks.e24n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e24n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e24n.left 0)=integerCoefficients (BasisData.rf24).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e24n.target0=affineShift (SourceBasis.rf24).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf24).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2224423508090917681459363840:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf24).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(2172288582120036798300160:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2224423508090917681459363840:ℤ)] (a-(83/256:ℝ))=(2224423508090917681459363840:ℝ) by simp [evalZ,horner]),(show evalZ [(2172288582120036798300160:ℤ)] (a-(83/256:ℝ))=(2172288582120036798300160:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf24] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf24).numerator.denominator = 2172288582120036798300160 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf24).numerator) (a-(83/256:ℝ)) /
      (2172288582120036798300160:ℝ) = (1/1840:ℝ)*evalZ (SourceBasis.rf24).numerator a
    simp only [SourceBasis.rf24]
    nlinarith [hh]
  · have hh := RFChecks.e24d.sound RFChecks.e24d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e24d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e24d.left 0)=factorCoefficients (BasisData.rf24).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e24d.target0=affineShift (SourceBasis.rf24).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf24).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(4503599627370496:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf24).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(4503599627370496:ℤ)] (a-(83/256:ℝ))=(4503599627370496:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf24] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf24).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf24).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/16:ℝ)*evalZ (SourceBasis.rf24).denominator a
    simp only [SourceBasis.rf24]
    nlinarith [hh]
  · norm_num [BasisData.rf24,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf25_translation (a : ℝ) :
    (BasisData.rf25).eval (a-83/256)=(SourceBasis.rf25).eval a := by
  apply translated_rf_of_scaled (BasisData.rf25) (SourceBasis.rf25) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e25n.sound RFChecks.e25n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e25n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e25n.left 0)=integerCoefficients (BasisData.rf25).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e25n.target0=affineShift (SourceBasis.rf25).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf25).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1112211754045458840729681920:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf25).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(67884018191251149946880:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1112211754045458840729681920:ℤ)] (a-(83/256:ℝ))=(1112211754045458840729681920:ℝ) by simp [evalZ,horner]),(show evalZ [(67884018191251149946880:ℤ)] (a-(83/256:ℝ))=(67884018191251149946880:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf25] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf25).numerator.denominator = 67884018191251149946880 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf25).numerator) (a-(83/256:ℝ)) /
      (67884018191251149946880:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf25).numerator a
    simp only [SourceBasis.rf25]
    nlinarith [hh]
  · have hh := RFChecks.e25d.sound RFChecks.e25d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e25d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e25d.left 0)=factorCoefficients (BasisData.rf25).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e25d.target0=affineShift (SourceBasis.rf25).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf25).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf25).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ))=(2251799813685248:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf25] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf25).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf25).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf25).denominator a
    simp only [SourceBasis.rf25]
    nlinarith [hh]
  · norm_num [BasisData.rf25,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf26_translation (a : ℝ) :
    (BasisData.rf26).eval (a-83/256)=(SourceBasis.rf26).eval a := by
  apply translated_rf_of_scaled (BasisData.rf26) (SourceBasis.rf26) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e26n.sound RFChecks.e26n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e26n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e26n.left 0)=integerCoefficients (BasisData.rf26).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e26n.target0=affineShift (SourceBasis.rf26).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf26).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1112211754045458840729681920:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf26).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(271536072765004599787520:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1112211754045458840729681920:ℤ)] (a-(83/256:ℝ))=(1112211754045458840729681920:ℝ) by simp [evalZ,horner]),(show evalZ [(271536072765004599787520:ℤ)] (a-(83/256:ℝ))=(271536072765004599787520:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf26] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf26).numerator.denominator = 271536072765004599787520 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf26).numerator) (a-(83/256:ℝ)) /
      (271536072765004599787520:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf26).numerator a
    simp only [SourceBasis.rf26]
    nlinarith [hh]
  · have hh := RFChecks.e26d.sound RFChecks.e26d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e26d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e26d.left 0)=factorCoefficients (BasisData.rf26).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e26d.target0=affineShift (SourceBasis.rf26).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf26).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf26).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ))=(2251799813685248:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf26] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf26).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf26).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf26).denominator a
    simp only [SourceBasis.rf26]
    nlinarith [hh]
  · norm_num [BasisData.rf26,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf27_translation (a : ℝ) :
    (BasisData.rf27).eval (a-83/256)=(SourceBasis.rf27).eval a := by
  apply translated_rf_of_scaled (BasisData.rf27) (SourceBasis.rf27) (1:ℝ) (1:ℝ) a (83/256)
  · have hh := RFChecks.e27n.sound RFChecks.e27n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e27n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e27n.left 0)=integerCoefficients (BasisData.rf27).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e27n.target0=affineShift (SourceBasis.rf27).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf27).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf27).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(1073741824:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),(show evalZ [(1073741824:ℤ)] (a-(83/256:ℝ))=(1073741824:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf27] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf27).numerator.denominator = 1073741824 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf27).numerator) (a-(83/256:ℝ)) /
      (1073741824:ℝ) = (1:ℝ)*evalZ (SourceBasis.rf27).numerator a
    simp only [SourceBasis.rf27]
    nlinarith [hh]
  · have hh := RFChecks.e27d.sound RFChecks.e27d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e27d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e27d.left 0)=factorCoefficients (BasisData.rf27).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e27d.target0=affineShift (SourceBasis.rf27).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf27).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(256:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf27).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(256:ℤ)] (a-(83/256:ℝ))=(256:ℝ) by simp [evalZ,horner]),(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf27] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf27).factors = 1 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf27).factors) (a-(83/256:ℝ)) /
      (1:ℝ) = (1:ℝ)*evalZ (SourceBasis.rf27).denominator a
    simp only [SourceBasis.rf27]
    nlinarith [hh]
  · norm_num [BasisData.rf27,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf28_translation (a : ℝ) :
    (BasisData.rf28).eval (a-83/256)=(SourceBasis.rf28).eval a := by
  apply translated_rf_of_scaled (BasisData.rf28) (SourceBasis.rf28) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e28n.sound RFChecks.e28n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e28n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e28n.left 0)=integerCoefficients (BasisData.rf28).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e28n.target0=affineShift (SourceBasis.rf28).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf28).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(16971004547812787486720:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf28).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(66292986514893701120:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(16971004547812787486720:ℤ)] (a-(83/256:ℝ))=(16971004547812787486720:ℝ) by simp [evalZ,horner]),(show evalZ [(66292986514893701120:ℤ)] (a-(83/256:ℝ))=(66292986514893701120:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf28] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf28).numerator.denominator = 66292986514893701120 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf28).numerator) (a-(83/256:ℝ)) /
      (66292986514893701120:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf28).numerator a
    simp only [SourceBasis.rf28]
    nlinarith [hh]
  · have hh := RFChecks.e28d.sound RFChecks.e28d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e28d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e28d.left 0)=factorCoefficients (BasisData.rf28).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e28d.target0=affineShift (SourceBasis.rf28).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf28).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf28).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ))=(576460752303423488:ℝ) by simp [evalZ,horner]),(show evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))=(281474976710656:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf28] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf28).factors = 281474976710656 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf28).factors) (a-(83/256:ℝ)) /
      (281474976710656:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf28).denominator a
    simp only [SourceBasis.rf28]
    nlinarith [hh]
  · norm_num [BasisData.rf28,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf29_translation (a : ℝ) :
    (BasisData.rf29).eval (a-83/256)=(SourceBasis.rf29).eval a := by
  apply translated_rf_of_scaled (BasisData.rf29) (SourceBasis.rf29) (1/920:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e29n.sound RFChecks.e29n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e29n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e29n.left 0)=integerCoefficients (BasisData.rf29).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e29n.target0=affineShift (SourceBasis.rf29).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf29).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(4344577164240073596600320:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf29).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(8485502273906393743360:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(4344577164240073596600320:ℤ)] (a-(83/256:ℝ))=(4344577164240073596600320:ℝ) by simp [evalZ,horner]),(show evalZ [(8485502273906393743360:ℤ)] (a-(83/256:ℝ))=(8485502273906393743360:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf29] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf29).numerator.denominator = 8485502273906393743360 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf29).numerator) (a-(83/256:ℝ)) /
      (8485502273906393743360:ℝ) = (1/920:ℝ)*evalZ (SourceBasis.rf29).numerator a
    simp only [SourceBasis.rf29]
    nlinarith [hh]
  · have hh := RFChecks.e29d.sound RFChecks.e29d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e29d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e29d.left 0)=factorCoefficients (BasisData.rf29).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e29d.target0=affineShift (SourceBasis.rf29).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf29).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf29).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(576460752303423488:ℤ)] (a-(83/256:ℝ))=(576460752303423488:ℝ) by simp [evalZ,horner]),(show evalZ [(281474976710656:ℤ)] (a-(83/256:ℝ))=(281474976710656:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf29] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf29).factors = 281474976710656 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf29).factors) (a-(83/256:ℝ)) /
      (281474976710656:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf29).denominator a
    simp only [SourceBasis.rf29]
    nlinarith [hh]
  · norm_num [BasisData.rf29,ThomsonNegative.Compact.Packed.qval]
  · norm_num

#print axioms rf20_translation
end ThomsonNegative.Certificate.Bridges
