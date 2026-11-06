import ThomsonNegative.Certificate.Bridges.RFChecks14
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
theorem rf140_translation (a : ℝ) :
    (BasisData.rf140).eval (a-83/256)=(SourceBasis.rf140).eval a := by
  apply translated_rf_of_scaled (BasisData.rf140) (SourceBasis.rf140) (1/20:ℝ) (1/4:ℝ) a (83/256)
  · have hh := RFChecks.e140n.sound RFChecks.e140n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e140n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e140n.left 0)=integerCoefficients (BasisData.rf140).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e140n.target0=affineShift (SourceBasis.rf140).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf140).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(5629499534213120:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf140).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(1374389534720:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(5629499534213120:ℤ)] (a-(83/256:ℝ))=(5629499534213120:ℝ) by simp [evalZ,horner]),(show evalZ [(1374389534720:ℤ)] (a-(83/256:ℝ))=(1374389534720:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf140] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf140).numerator.denominator = 1374389534720 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf140).numerator) (a-(83/256:ℝ)) /
      (1374389534720:ℝ) = (1/20:ℝ)*evalZ (SourceBasis.rf140).numerator a
    simp only [SourceBasis.rf140]
    nlinarith [hh]
  · have hh := RFChecks.e140d.sound RFChecks.e140d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e140d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e140d.left 0)=factorCoefficients (BasisData.rf140).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e140d.target0=affineShift (SourceBasis.rf140).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf140).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1125899906842624:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf140).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1125899906842624:ℤ)] (a-(83/256:ℝ))=(1125899906842624:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf140] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf140).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf140).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/4:ℝ)*evalZ (SourceBasis.rf140).denominator a
    simp only [SourceBasis.rf140]
    nlinarith [hh]
  · norm_num [BasisData.rf140,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf141_translation (a : ℝ) :
    (BasisData.rf141).eval (a-83/256)=(SourceBasis.rf141).eval a := by
  apply translated_rf_of_scaled (BasisData.rf141) (SourceBasis.rf141) (1/40:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e141n.sound RFChecks.e141n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e141n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e141n.left 0)=integerCoefficients (BasisData.rf141).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e141n.target0=affineShift (SourceBasis.rf141).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf141).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2882303761517117440:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf141).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(11258999068426240:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2882303761517117440:ℤ)] (a-(83/256:ℝ))=(2882303761517117440:ℝ) by simp [evalZ,horner]),(show evalZ [(11258999068426240:ℤ)] (a-(83/256:ℝ))=(11258999068426240:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf141] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf141).numerator.denominator = 11258999068426240 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf141).numerator) (a-(83/256:ℝ)) /
      (11258999068426240:ℝ) = (1/40:ℝ)*evalZ (SourceBasis.rf141).numerator a
    simp only [SourceBasis.rf141]
    nlinarith [hh]
  · have hh := RFChecks.e141d.sound RFChecks.e141d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e141d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e141d.left 0)=factorCoefficients (BasisData.rf141).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e141d.target0=affineShift (SourceBasis.rf141).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf141).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf141).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2251799813685248:ℤ)] (a-(83/256:ℝ))=(2251799813685248:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf141] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf141).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf141).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf141).denominator a
    simp only [SourceBasis.rf141]
    nlinarith [hh]
  · norm_num [BasisData.rf141,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf142_translation (a : ℝ) :
    (BasisData.rf142).eval (a-83/256)=(SourceBasis.rf142).eval a := by
  apply translated_rf_of_scaled (BasisData.rf142) (SourceBasis.rf142) (1/20:ℝ) (1/4:ℝ) a (83/256)
  · have hh := RFChecks.e142n.sound RFChecks.e142n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e142n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e142n.left 0)=integerCoefficients (BasisData.rf142).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e142n.target0=affineShift (SourceBasis.rf142).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf142).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1441151880758558720:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf142).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(351843720888320:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1441151880758558720:ℤ)] (a-(83/256:ℝ))=(1441151880758558720:ℝ) by simp [evalZ,horner]),(show evalZ [(351843720888320:ℤ)] (a-(83/256:ℝ))=(351843720888320:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf142] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf142).numerator.denominator = 351843720888320 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf142).numerator) (a-(83/256:ℝ)) /
      (351843720888320:ℝ) = (1/20:ℝ)*evalZ (SourceBasis.rf142).numerator a
    simp only [SourceBasis.rf142]
    nlinarith [hh]
  · have hh := RFChecks.e142d.sound RFChecks.e142d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e142d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e142d.left 0)=factorCoefficients (BasisData.rf142).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e142d.target0=affineShift (SourceBasis.rf142).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf142).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1125899906842624:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf142).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1125899906842624:ℤ)] (a-(83/256:ℝ))=(1125899906842624:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf142] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf142).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf142).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/4:ℝ)*evalZ (SourceBasis.rf142).denominator a
    simp only [SourceBasis.rf142]
    nlinarith [hh]
  · norm_num [BasisData.rf142,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf143_translation (a : ℝ) :
    (BasisData.rf143).eval (a-83/256)=(SourceBasis.rf143).eval a := by
  apply translated_rf_of_scaled (BasisData.rf143) (SourceBasis.rf143) (1/20:ℝ) (1/4:ℝ) a (83/256)
  · have hh := RFChecks.e143n.sound RFChecks.e143n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e143n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e143n.left 0)=integerCoefficients (BasisData.rf143).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e143n.target0=affineShift (SourceBasis.rf143).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf143).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1441151880758558720:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf143).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(1407374883553280:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1441151880758558720:ℤ)] (a-(83/256:ℝ))=(1441151880758558720:ℝ) by simp [evalZ,horner]),(show evalZ [(1407374883553280:ℤ)] (a-(83/256:ℝ))=(1407374883553280:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf143] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf143).numerator.denominator = 1407374883553280 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf143).numerator) (a-(83/256:ℝ)) /
      (1407374883553280:ℝ) = (1/20:ℝ)*evalZ (SourceBasis.rf143).numerator a
    simp only [SourceBasis.rf143]
    nlinarith [hh]
  · have hh := RFChecks.e143d.sound RFChecks.e143d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e143d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e143d.left 0)=factorCoefficients (BasisData.rf143).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e143d.target0=affineShift (SourceBasis.rf143).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf143).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(1125899906842624:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf143).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(1125899906842624:ℤ)] (a-(83/256:ℝ))=(1125899906842624:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf143] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf143).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf143).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/4:ℝ)*evalZ (SourceBasis.rf143).denominator a
    simp only [SourceBasis.rf143]
    nlinarith [hh]
  · norm_num [BasisData.rf143,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf144_translation (a : ℝ) :
    (BasisData.rf144).eval (a-83/256)=(SourceBasis.rf144).eval a := by
  apply translated_rf_of_scaled (BasisData.rf144) (SourceBasis.rf144) (1:ℝ) (1:ℝ) a (83/256)
  · have hh := RFChecks.e144n.sound RFChecks.e144n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e144n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e144n.left 0)=integerCoefficients (BasisData.rf144).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e144n.target0=affineShift (SourceBasis.rf144).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf144).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(16777216:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf144).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(32768:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(16777216:ℤ)] (a-(83/256:ℝ))=(16777216:ℝ) by simp [evalZ,horner]),(show evalZ [(32768:ℤ)] (a-(83/256:ℝ))=(32768:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf144] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf144).numerator.denominator = 32768 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf144).numerator) (a-(83/256:ℝ)) /
      (32768:ℝ) = (1:ℝ)*evalZ (SourceBasis.rf144).numerator a
    simp only [SourceBasis.rf144]
    nlinarith [hh]
  · have hh := RFChecks.e144d.sound RFChecks.e144d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e144d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e144d.left 0)=factorCoefficients (BasisData.rf144).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e144d.target0=affineShift (SourceBasis.rf144).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf144).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(65536:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf144).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(256:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(65536:ℤ)] (a-(83/256:ℝ))=(65536:ℝ) by simp [evalZ,horner]),(show evalZ [(256:ℤ)] (a-(83/256:ℝ))=(256:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf144] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf144).factors = 256 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf144).factors) (a-(83/256:ℝ)) /
      (256:ℝ) = (1:ℝ)*evalZ (SourceBasis.rf144).denominator a
    simp only [SourceBasis.rf144]
    nlinarith [hh]
  · norm_num [BasisData.rf144,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf145_translation (a : ℝ) :
    (BasisData.rf145).eval (a-83/256)=(SourceBasis.rf145).eval a := by
  apply translated_rf_of_scaled (BasisData.rf145) (SourceBasis.rf145) (1/60:ℝ) (1/12:ℝ) a (83/256)
  · have hh := RFChecks.e145n.sound RFChecks.e145n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e145n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e145n.left 0)=integerCoefficients (BasisData.rf145).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e145n.target0=affineShift (SourceBasis.rf145).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf145).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(16888498602639360:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf145).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(65970697666560:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(16888498602639360:ℤ)] (a-(83/256:ℝ))=(16888498602639360:ℝ) by simp [evalZ,horner]),(show evalZ [(65970697666560:ℤ)] (a-(83/256:ℝ))=(65970697666560:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf145] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf145).numerator.denominator = 65970697666560 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf145).numerator) (a-(83/256:ℝ)) /
      (65970697666560:ℝ) = (1/60:ℝ)*evalZ (SourceBasis.rf145).numerator a
    simp only [SourceBasis.rf145]
    nlinarith [hh]
  · have hh := RFChecks.e145d.sound RFChecks.e145d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e145d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e145d.left 0)=factorCoefficients (BasisData.rf145).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e145d.target0=affineShift (SourceBasis.rf145).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf145).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(3377699720527872:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf145).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(3377699720527872:ℤ)] (a-(83/256:ℝ))=(3377699720527872:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf145] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf145).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf145).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/12:ℝ)*evalZ (SourceBasis.rf145).denominator a
    simp only [SourceBasis.rf145]
    nlinarith [hh]
  · norm_num [BasisData.rf145,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf146_translation (a : ℝ) :
    (BasisData.rf146).eval (a-83/256)=(SourceBasis.rf146).eval a := by
  apply translated_rf_of_scaled (BasisData.rf146) (SourceBasis.rf146) (1/60:ℝ) (1/12:ℝ) a (83/256)
  · have hh := RFChecks.e146n.sound RFChecks.e146n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e146n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e146n.left 0)=integerCoefficients (BasisData.rf146).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e146n.target0=affineShift (SourceBasis.rf146).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf146).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(4323455642275676160:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf146).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(4222124650659840:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(4323455642275676160:ℤ)] (a-(83/256:ℝ))=(4323455642275676160:ℝ) by simp [evalZ,horner]),(show evalZ [(4222124650659840:ℤ)] (a-(83/256:ℝ))=(4222124650659840:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf146] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf146).numerator.denominator = 4222124650659840 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf146).numerator) (a-(83/256:ℝ)) /
      (4222124650659840:ℝ) = (1/60:ℝ)*evalZ (SourceBasis.rf146).numerator a
    simp only [SourceBasis.rf146]
    nlinarith [hh]
  · have hh := RFChecks.e146d.sound RFChecks.e146d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e146d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e146d.left 0)=factorCoefficients (BasisData.rf146).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e146d.target0=affineShift (SourceBasis.rf146).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf146).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(3377699720527872:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf146).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(3377699720527872:ℤ)] (a-(83/256:ℝ))=(3377699720527872:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf146] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf146).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf146).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/12:ℝ)*evalZ (SourceBasis.rf146).denominator a
    simp only [SourceBasis.rf146]
    nlinarith [hh]
  · norm_num [BasisData.rf146,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf147_translation (a : ℝ) :
    (BasisData.rf147).eval (a-83/256)=(SourceBasis.rf147).eval a := by
  apply translated_rf_of_scaled (BasisData.rf147) (SourceBasis.rf147) (1/60:ℝ) (1/12:ℝ) a (83/256)
  · have hh := RFChecks.e147n.sound RFChecks.e147n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e147n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e147n.left 0)=integerCoefficients (BasisData.rf147).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e147n.target0=affineShift (SourceBasis.rf147).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf147).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(4323455642275676160:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf147).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(131941395333120:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(4323455642275676160:ℤ)] (a-(83/256:ℝ))=(4323455642275676160:ℝ) by simp [evalZ,horner]),(show evalZ [(131941395333120:ℤ)] (a-(83/256:ℝ))=(131941395333120:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf147] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf147).numerator.denominator = 131941395333120 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf147).numerator) (a-(83/256:ℝ)) /
      (131941395333120:ℝ) = (1/60:ℝ)*evalZ (SourceBasis.rf147).numerator a
    simp only [SourceBasis.rf147]
    nlinarith [hh]
  · have hh := RFChecks.e147d.sound RFChecks.e147d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e147d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e147d.left 0)=factorCoefficients (BasisData.rf147).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e147d.target0=affineShift (SourceBasis.rf147).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf147).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(3377699720527872:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf147).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(3377699720527872:ℤ)] (a-(83/256:ℝ))=(3377699720527872:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf147] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf147).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf147).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/12:ℝ)*evalZ (SourceBasis.rf147).denominator a
    simp only [SourceBasis.rf147]
    nlinarith [hh]
  · norm_num [BasisData.rf147,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf148_translation (a : ℝ) :
    (BasisData.rf148).eval (a-83/256)=(SourceBasis.rf148).eval a := by
  apply translated_rf_of_scaled (BasisData.rf148) (SourceBasis.rf148) (1/3:ℝ) (1/3:ℝ) a (83/256)
  · have hh := RFChecks.e148n.sound RFChecks.e148n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e148n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e148n.left 0)=integerCoefficients (BasisData.rf148).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e148n.target0=affineShift (SourceBasis.rf148).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf148).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(50331648:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf148).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(98304:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(50331648:ℤ)] (a-(83/256:ℝ))=(50331648:ℝ) by simp [evalZ,horner]),(show evalZ [(98304:ℤ)] (a-(83/256:ℝ))=(98304:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf148] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf148).numerator.denominator = 98304 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf148).numerator) (a-(83/256:ℝ)) /
      (98304:ℝ) = (1/3:ℝ)*evalZ (SourceBasis.rf148).numerator a
    simp only [SourceBasis.rf148]
    nlinarith [hh]
  · have hh := RFChecks.e148d.sound RFChecks.e148d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e148d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e148d.left 0)=factorCoefficients (BasisData.rf148).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e148d.target0=affineShift (SourceBasis.rf148).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf148).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(196608:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf148).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(256:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(196608:ℤ)] (a-(83/256:ℝ))=(196608:ℝ) by simp [evalZ,horner]),(show evalZ [(256:ℤ)] (a-(83/256:ℝ))=(256:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf148] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf148).factors = 256 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf148).factors) (a-(83/256:ℝ)) /
      (256:ℝ) = (1/3:ℝ)*evalZ (SourceBasis.rf148).denominator a
    simp only [SourceBasis.rf148]
    nlinarith [hh]
  · norm_num [BasisData.rf148,ThomsonNegative.Compact.Packed.qval]
  · norm_num

#print axioms rf140_translation
end ThomsonNegative.Certificate.Bridges
