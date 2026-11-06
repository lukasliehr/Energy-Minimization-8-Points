import ThomsonNegative.Certificate.Bridges.RFChecks13
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
theorem rf130_translation (a : ℝ) :
    (BasisData.rf130).eval (a-83/256)=(SourceBasis.rf130).eval a := by
  apply translated_rf_of_scaled (BasisData.rf130) (SourceBasis.rf130) (1/40:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e130n.sound RFChecks.e130n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e130n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e130n.left 0)=integerCoefficients (BasisData.rf130).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e130n.target0=affineShift (SourceBasis.rf130).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf130).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(737869762948382064640:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf130).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(2882303761517117440:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(737869762948382064640:ℤ)] (a-(83/256:ℝ))=(737869762948382064640:ℝ) by simp [evalZ,horner]),(show evalZ [(2882303761517117440:ℤ)] (a-(83/256:ℝ))=(2882303761517117440:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf130] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf130).numerator.denominator = 2882303761517117440 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf130).numerator) (a-(83/256:ℝ)) /
      (2882303761517117440:ℝ) = (1/40:ℝ)*evalZ (SourceBasis.rf130).numerator a
    simp only [SourceBasis.rf130]
    nlinarith [hh]
  · have hh := RFChecks.e130d.sound RFChecks.e130d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e130d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e130d.left 0)=factorCoefficients (BasisData.rf130).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e130d.target0=affineShift (SourceBasis.rf130).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf130).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf130).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ))=(2251799813685248:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf130] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf130).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf130).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf130).denominator a
    simp only [SourceBasis.rf130]
    nlinarith [hh]
  · norm_num [BasisData.rf130,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf131_translation (a : ℝ) :
    (BasisData.rf131).eval (a-83/256)=(SourceBasis.rf131).eval a := by
  apply translated_rf_of_scaled (BasisData.rf131) (SourceBasis.rf131) (1/20:ℝ) (1/4:ℝ) a (83/256)
  · have hh := RFChecks.e131n.sound RFChecks.e131n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e131n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e131n.left 0)=integerCoefficients (BasisData.rf131).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e131n.target0=affineShift (SourceBasis.rf131).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf131).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(368934881474191032320:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf131).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(90071992547409920:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(368934881474191032320:ℤ)] (a-(83/256:ℝ))=(368934881474191032320:ℝ) by simp [evalZ,horner]),(show evalZ [(90071992547409920:ℤ)] (a-(83/256:ℝ))=(90071992547409920:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf131] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf131).numerator.denominator = 90071992547409920 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf131).numerator) (a-(83/256:ℝ)) /
      (90071992547409920:ℝ) = (1/20:ℝ)*evalZ (SourceBasis.rf131).numerator a
    simp only [SourceBasis.rf131]
    nlinarith [hh]
  · have hh := RFChecks.e131d.sound RFChecks.e131d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e131d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e131d.left 0)=factorCoefficients (BasisData.rf131).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e131d.target0=affineShift (SourceBasis.rf131).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf131).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1125899906842624:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf131).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1125899906842624:ℤ)] (a-(83/256:ℝ))=(1125899906842624:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf131] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf131).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf131).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/4:ℝ)*evalZ (SourceBasis.rf131).denominator a
    simp only [SourceBasis.rf131]
    nlinarith [hh]
  · norm_num [BasisData.rf131,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf132_translation (a : ℝ) :
    (BasisData.rf132).eval (a-83/256)=(SourceBasis.rf132).eval a := by
  apply translated_rf_of_scaled (BasisData.rf132) (SourceBasis.rf132) (1/20:ℝ) (1/4:ℝ) a (83/256)
  · have hh := RFChecks.e132n.sound RFChecks.e132n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e132n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e132n.left 0)=integerCoefficients (BasisData.rf132).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e132n.target0=affineShift (SourceBasis.rf132).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf132).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(368934881474191032320:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf132).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(360287970189639680:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(368934881474191032320:ℤ)] (a-(83/256:ℝ))=(368934881474191032320:ℝ) by simp [evalZ,horner]),(show evalZ [(360287970189639680:ℤ)] (a-(83/256:ℝ))=(360287970189639680:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf132] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf132).numerator.denominator = 360287970189639680 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf132).numerator) (a-(83/256:ℝ)) /
      (360287970189639680:ℝ) = (1/20:ℝ)*evalZ (SourceBasis.rf132).numerator a
    simp only [SourceBasis.rf132]
    nlinarith [hh]
  · have hh := RFChecks.e132d.sound RFChecks.e132d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e132d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e132d.left 0)=factorCoefficients (BasisData.rf132).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e132d.target0=affineShift (SourceBasis.rf132).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf132).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1125899906842624:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf132).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1125899906842624:ℤ)] (a-(83/256:ℝ))=(1125899906842624:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf132] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf132).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf132).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/4:ℝ)*evalZ (SourceBasis.rf132).denominator a
    simp only [SourceBasis.rf132]
    nlinarith [hh]
  · norm_num [BasisData.rf132,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf133_translation (a : ℝ) :
    (BasisData.rf133).eval (a-83/256)=(SourceBasis.rf133).eval a := by
  apply translated_rf_of_scaled (BasisData.rf133) (SourceBasis.rf133) (1:ℝ) (1:ℝ) a (83/256)
  · have hh := RFChecks.e133n.sound RFChecks.e133n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e133n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e133n.left 0)=integerCoefficients (BasisData.rf133).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e133n.target0=affineShift (SourceBasis.rf133).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf133).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(4294967296:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf133).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(8388608:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),(show evalZ [(8388608:ℤ)] (a-(83/256:ℝ))=(8388608:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf133] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf133).numerator.denominator = 8388608 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf133).numerator) (a-(83/256:ℝ)) /
      (8388608:ℝ) = (1:ℝ)*evalZ (SourceBasis.rf133).numerator a
    simp only [SourceBasis.rf133]
    nlinarith [hh]
  · have hh := RFChecks.e133d.sound RFChecks.e133d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e133d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e133d.left 0)=factorCoefficients (BasisData.rf133).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e133d.target0=affineShift (SourceBasis.rf133).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf133).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(65536:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf133).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(256:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(65536:ℤ)] (a-(83/256:ℝ))=(65536:ℝ) by simp [evalZ,horner]),(show evalZ [(256:ℤ)] (a-(83/256:ℝ))=(256:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf133] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf133).factors = 256 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf133).factors) (a-(83/256:ℝ)) /
      (256:ℝ) = (1:ℝ)*evalZ (SourceBasis.rf133).denominator a
    simp only [SourceBasis.rf133]
    nlinarith [hh]
  · norm_num [BasisData.rf133,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf134_translation (a : ℝ) :
    (BasisData.rf134).eval (a-83/256)=(SourceBasis.rf134).eval a := by
  apply translated_rf_of_scaled (BasisData.rf134) (SourceBasis.rf134) (1/60:ℝ) (1/12:ℝ) a (83/256)
  · have hh := RFChecks.e134n.sound RFChecks.e134n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e134n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e134n.left 0)=integerCoefficients (BasisData.rf134).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e134n.target0=affineShift (SourceBasis.rf134).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf134).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(4323455642275676160:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf134).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(16888498602639360:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(4323455642275676160:ℤ)] (a-(83/256:ℝ))=(4323455642275676160:ℝ) by simp [evalZ,horner]),(show evalZ [(16888498602639360:ℤ)] (a-(83/256:ℝ))=(16888498602639360:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf134] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf134).numerator.denominator = 16888498602639360 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf134).numerator) (a-(83/256:ℝ)) /
      (16888498602639360:ℝ) = (1/60:ℝ)*evalZ (SourceBasis.rf134).numerator a
    simp only [SourceBasis.rf134]
    nlinarith [hh]
  · have hh := RFChecks.e134d.sound RFChecks.e134d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e134d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e134d.left 0)=factorCoefficients (BasisData.rf134).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e134d.target0=affineShift (SourceBasis.rf134).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf134).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(3377699720527872:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf134).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(3377699720527872:ℤ)] (a-(83/256:ℝ))=(3377699720527872:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf134] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf134).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf134).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/12:ℝ)*evalZ (SourceBasis.rf134).denominator a
    simp only [SourceBasis.rf134]
    nlinarith [hh]
  · norm_num [BasisData.rf134,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf135_translation (a : ℝ) :
    (BasisData.rf135).eval (a-83/256)=(SourceBasis.rf135).eval a := by
  apply translated_rf_of_scaled (BasisData.rf135) (SourceBasis.rf135) (1/60:ℝ) (1/12:ℝ) a (83/256)
  · have hh := RFChecks.e135n.sound RFChecks.e135n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e135n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e135n.left 0)=integerCoefficients (BasisData.rf135).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e135n.target0=affineShift (SourceBasis.rf135).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf135).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1106804644422573096960:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf135).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(2161727821137838080:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1106804644422573096960:ℤ)] (a-(83/256:ℝ))=(1106804644422573096960:ℝ) by simp [evalZ,horner]),(show evalZ [(2161727821137838080:ℤ)] (a-(83/256:ℝ))=(2161727821137838080:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf135] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf135).numerator.denominator = 2161727821137838080 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf135).numerator) (a-(83/256:ℝ)) /
      (2161727821137838080:ℝ) = (1/60:ℝ)*evalZ (SourceBasis.rf135).numerator a
    simp only [SourceBasis.rf135]
    nlinarith [hh]
  · have hh := RFChecks.e135d.sound RFChecks.e135d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e135d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e135d.left 0)=factorCoefficients (BasisData.rf135).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e135d.target0=affineShift (SourceBasis.rf135).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf135).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(3377699720527872:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf135).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(3377699720527872:ℤ)] (a-(83/256:ℝ))=(3377699720527872:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf135] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf135).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf135).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/12:ℝ)*evalZ (SourceBasis.rf135).denominator a
    simp only [SourceBasis.rf135]
    nlinarith [hh]
  · norm_num [BasisData.rf135,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf136_translation (a : ℝ) :
    (BasisData.rf136).eval (a-83/256)=(SourceBasis.rf136).eval a := by
  apply translated_rf_of_scaled (BasisData.rf136) (SourceBasis.rf136) (1/60:ℝ) (1/12:ℝ) a (83/256)
  · have hh := RFChecks.e136n.sound RFChecks.e136n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e136n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e136n.left 0)=integerCoefficients (BasisData.rf136).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e136n.target0=affineShift (SourceBasis.rf136).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf136).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1106804644422573096960:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf136).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(2161727821137838080:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1106804644422573096960:ℤ)] (a-(83/256:ℝ))=(1106804644422573096960:ℝ) by simp [evalZ,horner]),(show evalZ [(2161727821137838080:ℤ)] (a-(83/256:ℝ))=(2161727821137838080:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf136] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf136).numerator.denominator = 2161727821137838080 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf136).numerator) (a-(83/256:ℝ)) /
      (2161727821137838080:ℝ) = (1/60:ℝ)*evalZ (SourceBasis.rf136).numerator a
    simp only [SourceBasis.rf136]
    nlinarith [hh]
  · have hh := RFChecks.e136d.sound RFChecks.e136d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e136d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e136d.left 0)=factorCoefficients (BasisData.rf136).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e136d.target0=affineShift (SourceBasis.rf136).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf136).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(3377699720527872:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf136).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(3377699720527872:ℤ)] (a-(83/256:ℝ))=(3377699720527872:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf136] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf136).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf136).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/12:ℝ)*evalZ (SourceBasis.rf136).denominator a
    simp only [SourceBasis.rf136]
    nlinarith [hh]
  · norm_num [BasisData.rf136,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf137_translation (a : ℝ) :
    (BasisData.rf137).eval (a-83/256)=(SourceBasis.rf137).eval a := by
  apply translated_rf_of_scaled (BasisData.rf137) (SourceBasis.rf137) (1/3:ℝ) (1/3:ℝ) a (83/256)
  · have hh := RFChecks.e137n.sound RFChecks.e137n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e137n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e137n.left 0)=integerCoefficients (BasisData.rf137).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e137n.target0=affineShift (SourceBasis.rf137).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf137).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(12884901888:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf137).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(50331648:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(12884901888:ℤ)] (a-(83/256:ℝ))=(12884901888:ℝ) by simp [evalZ,horner]),(show evalZ [(50331648:ℤ)] (a-(83/256:ℝ))=(50331648:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf137] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf137).numerator.denominator = 50331648 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf137).numerator) (a-(83/256:ℝ)) /
      (50331648:ℝ) = (1/3:ℝ)*evalZ (SourceBasis.rf137).numerator a
    simp only [SourceBasis.rf137]
    nlinarith [hh]
  · have hh := RFChecks.e137d.sound RFChecks.e137d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e137d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e137d.left 0)=factorCoefficients (BasisData.rf137).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e137d.target0=affineShift (SourceBasis.rf137).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf137).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(196608:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf137).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(256:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(196608:ℤ)] (a-(83/256:ℝ))=(196608:ℝ) by simp [evalZ,horner]),(show evalZ [(256:ℤ)] (a-(83/256:ℝ))=(256:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf137] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf137).factors = 256 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf137).factors) (a-(83/256:ℝ)) /
      (256:ℝ) = (1/3:ℝ)*evalZ (SourceBasis.rf137).denominator a
    simp only [SourceBasis.rf137]
    nlinarith [hh]
  · norm_num [BasisData.rf137,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf138_translation (a : ℝ) :
    (BasisData.rf138).eval (a-83/256)=(SourceBasis.rf138).eval a := by
  apply translated_rf_of_scaled (BasisData.rf138) (SourceBasis.rf138) (1/20:ℝ) (1/4:ℝ) a (83/256)
  · have hh := RFChecks.e138n.sound RFChecks.e138n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e138n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e138n.left 0)=integerCoefficients (BasisData.rf138).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e138n.target0=affineShift (SourceBasis.rf138).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf138).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(21990232555520:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf138).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(85899345920:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(21990232555520:ℤ)] (a-(83/256:ℝ))=(21990232555520:ℝ) by simp [evalZ,horner]),(show evalZ [(85899345920:ℤ)] (a-(83/256:ℝ))=(85899345920:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf138] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf138).numerator.denominator = 85899345920 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf138).numerator) (a-(83/256:ℝ)) /
      (85899345920:ℝ) = (1/20:ℝ)*evalZ (SourceBasis.rf138).numerator a
    simp only [SourceBasis.rf138]
    nlinarith [hh]
  · have hh := RFChecks.e138d.sound RFChecks.e138d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e138d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e138d.left 0)=factorCoefficients (BasisData.rf138).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e138d.target0=affineShift (SourceBasis.rf138).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf138).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1125899906842624:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf138).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1125899906842624:ℤ)] (a-(83/256:ℝ))=(1125899906842624:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf138] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf138).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf138).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/4:ℝ)*evalZ (SourceBasis.rf138).denominator a
    simp only [SourceBasis.rf138]
    nlinarith [hh]
  · norm_num [BasisData.rf138,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf139_translation (a : ℝ) :
    (BasisData.rf139).eval (a-83/256)=(SourceBasis.rf139).eval a := by
  apply translated_rf_of_scaled (BasisData.rf139) (SourceBasis.rf139) (1/20:ℝ) (1/4:ℝ) a (83/256)
  · have hh := RFChecks.e139n.sound RFChecks.e139n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e139n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e139n.left 0)=integerCoefficients (BasisData.rf139).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e139n.target0=affineShift (SourceBasis.rf139).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf139).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(5629499534213120:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf139).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(10995116277760:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(5629499534213120:ℤ)] (a-(83/256:ℝ))=(5629499534213120:ℝ) by simp [evalZ,horner]),(show evalZ [(10995116277760:ℤ)] (a-(83/256:ℝ))=(10995116277760:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf139] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf139).numerator.denominator = 10995116277760 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf139).numerator) (a-(83/256:ℝ)) /
      (10995116277760:ℝ) = (1/20:ℝ)*evalZ (SourceBasis.rf139).numerator a
    simp only [SourceBasis.rf139]
    nlinarith [hh]
  · have hh := RFChecks.e139d.sound RFChecks.e139d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e139d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e139d.left 0)=factorCoefficients (BasisData.rf139).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e139d.target0=affineShift (SourceBasis.rf139).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf139).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1125899906842624:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf139).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1125899906842624:ℤ)] (a-(83/256:ℝ))=(1125899906842624:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf139] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf139).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf139).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/4:ℝ)*evalZ (SourceBasis.rf139).denominator a
    simp only [SourceBasis.rf139]
    nlinarith [hh]
  · norm_num [BasisData.rf139,ThomsonNegative.Compact.Packed.qval]
  · norm_num

#print axioms rf130_translation
end ThomsonNegative.Certificate.Bridges
