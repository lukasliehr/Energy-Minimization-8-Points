import ThomsonNegative.Certificate.Bridges.RFChecks12
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
theorem rf120_translation (a : ℝ) :
    (BasisData.rf120).eval (a-83/256)=(SourceBasis.rf120).eval a := by
  apply translated_rf_of_scaled (BasisData.rf120) (SourceBasis.rf120) (1/20:ℝ) (1/4:ℝ) a (83/256)
  · have hh := RFChecks.e120n.sound RFChecks.e120n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e120n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e120n.left 0)=integerCoefficients (BasisData.rf120).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e120n.target0=affineShift (SourceBasis.rf120).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf120).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1441151880758558720:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf120).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(351843720888320:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1441151880758558720:ℤ)] (a-(83/256:ℝ))=(1441151880758558720:ℝ) by simp [evalZ,horner]),(show evalZ [(351843720888320:ℤ)] (a-(83/256:ℝ))=(351843720888320:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf120] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf120).numerator.denominator = 351843720888320 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf120).numerator) (a-(83/256:ℝ)) /
      (351843720888320:ℝ) = (1/20:ℝ)*evalZ (SourceBasis.rf120).numerator a
    simp only [SourceBasis.rf120]
    nlinarith [hh]
  · have hh := RFChecks.e120d.sound RFChecks.e120d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e120d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e120d.left 0)=factorCoefficients (BasisData.rf120).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e120d.target0=affineShift (SourceBasis.rf120).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf120).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(4398046511104:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf120).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(4398046511104:ℤ)] (a-(83/256:ℝ))=(4398046511104:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf120] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf120).factors = 4294967296 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf120).factors) (a-(83/256:ℝ)) /
      (4294967296:ℝ) = (1/4:ℝ)*evalZ (SourceBasis.rf120).denominator a
    simp only [SourceBasis.rf120]
    nlinarith [hh]
  · norm_num [BasisData.rf120,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf121_translation (a : ℝ) :
    (BasisData.rf121).eval (a-83/256)=(SourceBasis.rf121).eval a := by
  apply translated_rf_of_scaled (BasisData.rf121) (SourceBasis.rf121) (1/20:ℝ) (1/4:ℝ) a (83/256)
  · have hh := RFChecks.e121n.sound RFChecks.e121n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e121n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e121n.left 0)=integerCoefficients (BasisData.rf121).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e121n.target0=affineShift (SourceBasis.rf121).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf121).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1441151880758558720:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf121).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(1407374883553280:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1441151880758558720:ℤ)] (a-(83/256:ℝ))=(1441151880758558720:ℝ) by simp [evalZ,horner]),(show evalZ [(1407374883553280:ℤ)] (a-(83/256:ℝ))=(1407374883553280:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf121] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf121).numerator.denominator = 1407374883553280 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf121).numerator) (a-(83/256:ℝ)) /
      (1407374883553280:ℝ) = (1/20:ℝ)*evalZ (SourceBasis.rf121).numerator a
    simp only [SourceBasis.rf121]
    nlinarith [hh]
  · have hh := RFChecks.e121d.sound RFChecks.e121d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e121d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e121d.left 0)=factorCoefficients (BasisData.rf121).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e121d.target0=affineShift (SourceBasis.rf121).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf121).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(4398046511104:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf121).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(4398046511104:ℤ)] (a-(83/256:ℝ))=(4398046511104:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf121] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf121).factors = 4294967296 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf121).factors) (a-(83/256:ℝ)) /
      (4294967296:ℝ) = (1/4:ℝ)*evalZ (SourceBasis.rf121).denominator a
    simp only [SourceBasis.rf121]
    nlinarith [hh]
  · norm_num [BasisData.rf121,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf122_translation (a : ℝ) :
    (BasisData.rf122).eval (a-83/256)=(SourceBasis.rf122).eval a := by
  apply translated_rf_of_scaled (BasisData.rf122) (SourceBasis.rf122) (1:ℝ) (1:ℝ) a (83/256)
  · have hh := RFChecks.e122n.sound RFChecks.e122n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e122n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e122n.left 0)=integerCoefficients (BasisData.rf122).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e122n.target0=affineShift (SourceBasis.rf122).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf122).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(4294967296:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf122).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(8388608:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),(show evalZ [(8388608:ℤ)] (a-(83/256:ℝ))=(8388608:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf122] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf122).numerator.denominator = 8388608 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf122).numerator) (a-(83/256:ℝ)) /
      (8388608:ℝ) = (1:ℝ)*evalZ (SourceBasis.rf122).numerator a
    simp only [SourceBasis.rf122]
    nlinarith [hh]
  · have hh := RFChecks.e122d.sound RFChecks.e122d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e122d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e122d.left 0)=factorCoefficients (BasisData.rf122).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e122d.target0=affineShift (SourceBasis.rf122).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf122).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(65536:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf122).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(256:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(65536:ℤ)] (a-(83/256:ℝ))=(65536:ℝ) by simp [evalZ,horner]),(show evalZ [(256:ℤ)] (a-(83/256:ℝ))=(256:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf122] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf122).factors = 256 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf122).factors) (a-(83/256:ℝ)) /
      (256:ℝ) = (1:ℝ)*evalZ (SourceBasis.rf122).denominator a
    simp only [SourceBasis.rf122]
    nlinarith [hh]
  · norm_num [BasisData.rf122,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf123_translation (a : ℝ) :
    (BasisData.rf123).eval (a-83/256)=(SourceBasis.rf123).eval a := by
  apply translated_rf_of_scaled (BasisData.rf123) (SourceBasis.rf123) (1/60:ℝ) (1/12:ℝ) a (83/256)
  · have hh := RFChecks.e123n.sound RFChecks.e123n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e123n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e123n.left 0)=integerCoefficients (BasisData.rf123).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e123n.target0=affineShift (SourceBasis.rf123).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf123).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(4323455642275676160:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf123).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(8444249301319680:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(4323455642275676160:ℤ)] (a-(83/256:ℝ))=(4323455642275676160:ℝ) by simp [evalZ,horner]),(show evalZ [(8444249301319680:ℤ)] (a-(83/256:ℝ))=(8444249301319680:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf123] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf123).numerator.denominator = 8444249301319680 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf123).numerator) (a-(83/256:ℝ)) /
      (8444249301319680:ℝ) = (1/60:ℝ)*evalZ (SourceBasis.rf123).numerator a
    simp only [SourceBasis.rf123]
    nlinarith [hh]
  · have hh := RFChecks.e123d.sound RFChecks.e123d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e123d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e123d.left 0)=factorCoefficients (BasisData.rf123).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e123d.target0=affineShift (SourceBasis.rf123).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf123).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(13194139533312:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf123).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(13194139533312:ℤ)] (a-(83/256:ℝ))=(13194139533312:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf123] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf123).factors = 4294967296 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf123).factors) (a-(83/256:ℝ)) /
      (4294967296:ℝ) = (1/12:ℝ)*evalZ (SourceBasis.rf123).denominator a
    simp only [SourceBasis.rf123]
    nlinarith [hh]
  · norm_num [BasisData.rf123,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf124_translation (a : ℝ) :
    (BasisData.rf124).eval (a-83/256)=(SourceBasis.rf124).eval a := by
  apply translated_rf_of_scaled (BasisData.rf124) (SourceBasis.rf124) (1/60:ℝ) (1/12:ℝ) a (83/256)
  · have hh := RFChecks.e124n.sound RFChecks.e124n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e124n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e124n.left 0)=integerCoefficients (BasisData.rf124).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e124n.target0=affineShift (SourceBasis.rf124).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf124).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1106804644422573096960:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf124).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(1080863910568919040:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1106804644422573096960:ℤ)] (a-(83/256:ℝ))=(1106804644422573096960:ℝ) by simp [evalZ,horner]),(show evalZ [(1080863910568919040:ℤ)] (a-(83/256:ℝ))=(1080863910568919040:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf124] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf124).numerator.denominator = 1080863910568919040 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf124).numerator) (a-(83/256:ℝ)) /
      (1080863910568919040:ℝ) = (1/60:ℝ)*evalZ (SourceBasis.rf124).numerator a
    simp only [SourceBasis.rf124]
    nlinarith [hh]
  · have hh := RFChecks.e124d.sound RFChecks.e124d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e124d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e124d.left 0)=factorCoefficients (BasisData.rf124).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e124d.target0=affineShift (SourceBasis.rf124).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf124).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(13194139533312:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf124).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(13194139533312:ℤ)] (a-(83/256:ℝ))=(13194139533312:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf124] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf124).factors = 4294967296 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf124).factors) (a-(83/256:ℝ)) /
      (4294967296:ℝ) = (1/12:ℝ)*evalZ (SourceBasis.rf124).denominator a
    simp only [SourceBasis.rf124]
    nlinarith [hh]
  · norm_num [BasisData.rf124,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf125_translation (a : ℝ) :
    (BasisData.rf125).eval (a-83/256)=(SourceBasis.rf125).eval a := by
  apply translated_rf_of_scaled (BasisData.rf125) (SourceBasis.rf125) (1/60:ℝ) (1/12:ℝ) a (83/256)
  · have hh := RFChecks.e125n.sound RFChecks.e125n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e125n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e125n.left 0)=integerCoefficients (BasisData.rf125).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e125n.target0=affineShift (SourceBasis.rf125).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf125).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(4323455642275676160:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf125).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(2111062325329920:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(4323455642275676160:ℤ)] (a-(83/256:ℝ))=(4323455642275676160:ℝ) by simp [evalZ,horner]),(show evalZ [(2111062325329920:ℤ)] (a-(83/256:ℝ))=(2111062325329920:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf125] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf125).numerator.denominator = 2111062325329920 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf125).numerator) (a-(83/256:ℝ)) /
      (2111062325329920:ℝ) = (1/60:ℝ)*evalZ (SourceBasis.rf125).numerator a
    simp only [SourceBasis.rf125]
    nlinarith [hh]
  · have hh := RFChecks.e125d.sound RFChecks.e125d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e125d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e125d.left 0)=factorCoefficients (BasisData.rf125).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e125d.target0=affineShift (SourceBasis.rf125).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf125).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(13194139533312:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf125).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(13194139533312:ℤ)] (a-(83/256:ℝ))=(13194139533312:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf125] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf125).factors = 4294967296 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf125).factors) (a-(83/256:ℝ)) /
      (4294967296:ℝ) = (1/12:ℝ)*evalZ (SourceBasis.rf125).denominator a
    simp only [SourceBasis.rf125]
    nlinarith [hh]
  · norm_num [BasisData.rf125,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf126_translation (a : ℝ) :
    (BasisData.rf126).eval (a-83/256)=(SourceBasis.rf126).eval a := by
  apply translated_rf_of_scaled (BasisData.rf126) (SourceBasis.rf126) (1/3:ℝ) (1/3:ℝ) a (83/256)
  · have hh := RFChecks.e126n.sound RFChecks.e126n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e126n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e126n.left 0)=integerCoefficients (BasisData.rf126).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e126n.target0=affineShift (SourceBasis.rf126).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf126).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(12884901888:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf126).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(50331648:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(12884901888:ℤ)] (a-(83/256:ℝ))=(12884901888:ℝ) by simp [evalZ,horner]),(show evalZ [(50331648:ℤ)] (a-(83/256:ℝ))=(50331648:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf126] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf126).numerator.denominator = 50331648 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf126).numerator) (a-(83/256:ℝ)) /
      (50331648:ℝ) = (1/3:ℝ)*evalZ (SourceBasis.rf126).numerator a
    simp only [SourceBasis.rf126]
    nlinarith [hh]
  · have hh := RFChecks.e126d.sound RFChecks.e126d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e126d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e126d.left 0)=factorCoefficients (BasisData.rf126).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e126d.target0=affineShift (SourceBasis.rf126).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf126).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(196608:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf126).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(256:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(196608:ℤ)] (a-(83/256:ℝ))=(196608:ℝ) by simp [evalZ,horner]),(show evalZ [(256:ℤ)] (a-(83/256:ℝ))=(256:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf126] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf126).factors = 256 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf126).factors) (a-(83/256:ℝ)) /
      (256:ℝ) = (1/3:ℝ)*evalZ (SourceBasis.rf126).denominator a
    simp only [SourceBasis.rf126]
    nlinarith [hh]
  · norm_num [BasisData.rf126,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf127_translation (a : ℝ) :
    (BasisData.rf127).eval (a-83/256)=(SourceBasis.rf127).eval a := by
  apply translated_rf_of_scaled (BasisData.rf127) (SourceBasis.rf127) (1/20:ℝ) (1/4:ℝ) a (83/256)
  · have hh := RFChecks.e127n.sound RFChecks.e127n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e127n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e127n.left 0)=integerCoefficients (BasisData.rf127).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e127n.target0=affineShift (SourceBasis.rf127).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf127).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(5629499534213120:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf127).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(21990232555520:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(5629499534213120:ℤ)] (a-(83/256:ℝ))=(5629499534213120:ℝ) by simp [evalZ,horner]),(show evalZ [(21990232555520:ℤ)] (a-(83/256:ℝ))=(21990232555520:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf127] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf127).numerator.denominator = 21990232555520 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf127).numerator) (a-(83/256:ℝ)) /
      (21990232555520:ℝ) = (1/20:ℝ)*evalZ (SourceBasis.rf127).numerator a
    simp only [SourceBasis.rf127]
    nlinarith [hh]
  · have hh := RFChecks.e127d.sound RFChecks.e127d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e127d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e127d.left 0)=factorCoefficients (BasisData.rf127).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e127d.target0=affineShift (SourceBasis.rf127).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf127).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1125899906842624:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf127).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1125899906842624:ℤ)] (a-(83/256:ℝ))=(1125899906842624:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf127] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf127).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf127).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/4:ℝ)*evalZ (SourceBasis.rf127).denominator a
    simp only [SourceBasis.rf127]
    nlinarith [hh]
  · norm_num [BasisData.rf127,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf128_translation (a : ℝ) :
    (BasisData.rf128).eval (a-83/256)=(SourceBasis.rf128).eval a := by
  apply translated_rf_of_scaled (BasisData.rf128) (SourceBasis.rf128) (1/20:ℝ) (1/4:ℝ) a (83/256)
  · have hh := RFChecks.e128n.sound RFChecks.e128n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e128n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e128n.left 0)=integerCoefficients (BasisData.rf128).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e128n.target0=affineShift (SourceBasis.rf128).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf128).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1441151880758558720:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf128).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(2814749767106560:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1441151880758558720:ℤ)] (a-(83/256:ℝ))=(1441151880758558720:ℝ) by simp [evalZ,horner]),(show evalZ [(2814749767106560:ℤ)] (a-(83/256:ℝ))=(2814749767106560:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf128] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf128).numerator.denominator = 2814749767106560 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf128).numerator) (a-(83/256:ℝ)) /
      (2814749767106560:ℝ) = (1/20:ℝ)*evalZ (SourceBasis.rf128).numerator a
    simp only [SourceBasis.rf128]
    nlinarith [hh]
  · have hh := RFChecks.e128d.sound RFChecks.e128d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e128d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e128d.left 0)=factorCoefficients (BasisData.rf128).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e128d.target0=affineShift (SourceBasis.rf128).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf128).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1125899906842624:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf128).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1125899906842624:ℤ)] (a-(83/256:ℝ))=(1125899906842624:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf128] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf128).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf128).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/4:ℝ)*evalZ (SourceBasis.rf128).denominator a
    simp only [SourceBasis.rf128]
    nlinarith [hh]
  · norm_num [BasisData.rf128,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf129_translation (a : ℝ) :
    (BasisData.rf129).eval (a-83/256)=(SourceBasis.rf129).eval a := by
  apply translated_rf_of_scaled (BasisData.rf129) (SourceBasis.rf129) (1/20:ℝ) (1/4:ℝ) a (83/256)
  · have hh := RFChecks.e129n.sound RFChecks.e129n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e129n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e129n.left 0)=integerCoefficients (BasisData.rf129).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e129n.target0=affineShift (SourceBasis.rf129).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf129).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1441151880758558720:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf129).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(351843720888320:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1441151880758558720:ℤ)] (a-(83/256:ℝ))=(1441151880758558720:ℝ) by simp [evalZ,horner]),(show evalZ [(351843720888320:ℤ)] (a-(83/256:ℝ))=(351843720888320:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf129] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf129).numerator.denominator = 351843720888320 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf129).numerator) (a-(83/256:ℝ)) /
      (351843720888320:ℝ) = (1/20:ℝ)*evalZ (SourceBasis.rf129).numerator a
    simp only [SourceBasis.rf129]
    nlinarith [hh]
  · have hh := RFChecks.e129d.sound RFChecks.e129d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e129d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e129d.left 0)=factorCoefficients (BasisData.rf129).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e129d.target0=affineShift (SourceBasis.rf129).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf129).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1125899906842624:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf129).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1125899906842624:ℤ)] (a-(83/256:ℝ))=(1125899906842624:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf129] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf129).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf129).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/4:ℝ)*evalZ (SourceBasis.rf129).denominator a
    simp only [SourceBasis.rf129]
    nlinarith [hh]
  · norm_num [BasisData.rf129,ThomsonNegative.Compact.Packed.qval]
  · norm_num

#print axioms rf120_translation
end ThomsonNegative.Certificate.Bridges
