import ThomsonNegative.Certificate.Bridges.RFChecks08
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
theorem rf80_translation (a : ℝ) :
    (BasisData.rf80).eval (a-83/256)=(SourceBasis.rf80).eval a := by
  apply translated_rf_of_scaled (BasisData.rf80) (SourceBasis.rf80) (1/120:ℝ) (1/24:ℝ) a (83/256)
  · have hh := RFChecks.e80n.sound RFChecks.e80n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e80n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e80n.left 0)=integerCoefficients (BasisData.rf80).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e80n.target0=affineShift (SourceBasis.rf80).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf80).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2213609288845146193920:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf80).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(4323455642275676160:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2213609288845146193920:ℤ)] (a-(83/256:ℝ))=(2213609288845146193920:ℝ) by simp [evalZ,horner]),(show evalZ [(4323455642275676160:ℤ)] (a-(83/256:ℝ))=(4323455642275676160:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf80] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf80).numerator.denominator = 4323455642275676160 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf80).numerator) (a-(83/256:ℝ)) /
      (4323455642275676160:ℝ) = (1/120:ℝ)*evalZ (SourceBasis.rf80).numerator a
    simp only [SourceBasis.rf80]
    nlinarith [hh]
  · have hh := RFChecks.e80d.sound RFChecks.e80d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e80d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e80d.left 0)=factorCoefficients (BasisData.rf80).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e80d.target0=affineShift (SourceBasis.rf80).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf80).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(26388279066624:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf80).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(26388279066624:ℤ)] (a-(83/256:ℝ))=(26388279066624:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf80] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf80).factors = 4294967296 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf80).factors) (a-(83/256:ℝ)) /
      (4294967296:ℝ) = (1/24:ℝ)*evalZ (SourceBasis.rf80).denominator a
    simp only [SourceBasis.rf80]
    nlinarith [hh]
  · norm_num [BasisData.rf80,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf81_translation (a : ℝ) :
    (BasisData.rf81).eval (a-83/256)=(SourceBasis.rf81).eval a := by
  apply translated_rf_of_scaled (BasisData.rf81) (SourceBasis.rf81) (1/120:ℝ) (1/24:ℝ) a (83/256)
  · have hh := RFChecks.e81n.sound RFChecks.e81n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e81n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e81n.left 0)=integerCoefficients (BasisData.rf81).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e81n.target0=affineShift (SourceBasis.rf81).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf81).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2213609288845146193920:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf81).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(2161727821137838080:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2213609288845146193920:ℤ)] (a-(83/256:ℝ))=(2213609288845146193920:ℝ) by simp [evalZ,horner]),(show evalZ [(2161727821137838080:ℤ)] (a-(83/256:ℝ))=(2161727821137838080:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf81] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf81).numerator.denominator = 2161727821137838080 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf81).numerator) (a-(83/256:ℝ)) /
      (2161727821137838080:ℝ) = (1/120:ℝ)*evalZ (SourceBasis.rf81).numerator a
    simp only [SourceBasis.rf81]
    nlinarith [hh]
  · have hh := RFChecks.e81d.sound RFChecks.e81d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e81d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e81d.left 0)=factorCoefficients (BasisData.rf81).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e81d.target0=affineShift (SourceBasis.rf81).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf81).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(26388279066624:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf81).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(26388279066624:ℤ)] (a-(83/256:ℝ))=(26388279066624:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf81] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf81).factors = 4294967296 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf81).factors) (a-(83/256:ℝ)) /
      (4294967296:ℝ) = (1/24:ℝ)*evalZ (SourceBasis.rf81).denominator a
    simp only [SourceBasis.rf81]
    nlinarith [hh]
  · norm_num [BasisData.rf81,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf82_translation (a : ℝ) :
    (BasisData.rf82).eval (a-83/256)=(SourceBasis.rf82).eval a := by
  apply translated_rf_of_scaled (BasisData.rf82) (SourceBasis.rf82) (1/3:ℝ) (1/3:ℝ) a (83/256)
  · have hh := RFChecks.e82n.sound RFChecks.e82n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e82n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e82n.left 0)=integerCoefficients (BasisData.rf82).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e82n.target0=affineShift (SourceBasis.rf82).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf82).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(3298534883328:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf82).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(12884901888:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(3298534883328:ℤ)] (a-(83/256:ℝ))=(3298534883328:ℝ) by simp [evalZ,horner]),(show evalZ [(12884901888:ℤ)] (a-(83/256:ℝ))=(12884901888:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf82] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf82).numerator.denominator = 12884901888 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf82).numerator) (a-(83/256:ℝ)) /
      (12884901888:ℝ) = (1/3:ℝ)*evalZ (SourceBasis.rf82).numerator a
    simp only [SourceBasis.rf82]
    nlinarith [hh]
  · have hh := RFChecks.e82d.sound RFChecks.e82d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e82d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e82d.left 0)=factorCoefficients (BasisData.rf82).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e82d.target0=affineShift (SourceBasis.rf82).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf82).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(196608:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf82).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(256:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(196608:ℤ)] (a-(83/256:ℝ))=(196608:ℝ) by simp [evalZ,horner]),(show evalZ [(256:ℤ)] (a-(83/256:ℝ))=(256:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf82] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf82).factors = 256 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf82).factors) (a-(83/256:ℝ)) /
      (256:ℝ) = (1/3:ℝ)*evalZ (SourceBasis.rf82).denominator a
    simp only [SourceBasis.rf82]
    nlinarith [hh]
  · norm_num [BasisData.rf82,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf83_translation (a : ℝ) :
    (BasisData.rf83).eval (a-83/256)=(SourceBasis.rf83).eval a := by
  apply translated_rf_of_scaled (BasisData.rf83) (SourceBasis.rf83) (1/120:ℝ) (1/24:ℝ) a (83/256)
  · have hh := RFChecks.e83n.sound RFChecks.e83n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e83n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e83n.left 0)=integerCoefficients (BasisData.rf83).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e83n.target0=affineShift (SourceBasis.rf83).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf83).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(33776997205278720:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf83).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(131941395333120:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(33776997205278720:ℤ)] (a-(83/256:ℝ))=(33776997205278720:ℝ) by simp [evalZ,horner]),(show evalZ [(131941395333120:ℤ)] (a-(83/256:ℝ))=(131941395333120:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf83] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf83).numerator.denominator = 131941395333120 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf83).numerator) (a-(83/256:ℝ)) /
      (131941395333120:ℝ) = (1/120:ℝ)*evalZ (SourceBasis.rf83).numerator a
    simp only [SourceBasis.rf83]
    nlinarith [hh]
  · have hh := RFChecks.e83d.sound RFChecks.e83d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e83d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e83d.left 0)=factorCoefficients (BasisData.rf83).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e83d.target0=affineShift (SourceBasis.rf83).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf83).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(26388279066624:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf83).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(26388279066624:ℤ)] (a-(83/256:ℝ))=(26388279066624:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf83] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf83).factors = 4294967296 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf83).factors) (a-(83/256:ℝ)) /
      (4294967296:ℝ) = (1/24:ℝ)*evalZ (SourceBasis.rf83).denominator a
    simp only [SourceBasis.rf83]
    nlinarith [hh]
  · norm_num [BasisData.rf83,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf84_translation (a : ℝ) :
    (BasisData.rf84).eval (a-83/256)=(SourceBasis.rf84).eval a := by
  apply translated_rf_of_scaled (BasisData.rf84) (SourceBasis.rf84) (1/120:ℝ) (1/24:ℝ) a (83/256)
  · have hh := RFChecks.e84n.sound RFChecks.e84n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e84n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e84n.left 0)=integerCoefficients (BasisData.rf84).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e84n.target0=affineShift (SourceBasis.rf84).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf84).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(8646911284551352320:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf84).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(16888498602639360:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(8646911284551352320:ℤ)] (a-(83/256:ℝ))=(8646911284551352320:ℝ) by simp [evalZ,horner]),(show evalZ [(16888498602639360:ℤ)] (a-(83/256:ℝ))=(16888498602639360:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf84] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf84).numerator.denominator = 16888498602639360 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf84).numerator) (a-(83/256:ℝ)) /
      (16888498602639360:ℝ) = (1/120:ℝ)*evalZ (SourceBasis.rf84).numerator a
    simp only [SourceBasis.rf84]
    nlinarith [hh]
  · have hh := RFChecks.e84d.sound RFChecks.e84d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e84d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e84d.left 0)=factorCoefficients (BasisData.rf84).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e84d.target0=affineShift (SourceBasis.rf84).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf84).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(26388279066624:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf84).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(26388279066624:ℤ)] (a-(83/256:ℝ))=(26388279066624:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf84] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf84).factors = 4294967296 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf84).factors) (a-(83/256:ℝ)) /
      (4294967296:ℝ) = (1/24:ℝ)*evalZ (SourceBasis.rf84).denominator a
    simp only [SourceBasis.rf84]
    nlinarith [hh]
  · norm_num [BasisData.rf84,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf85_translation (a : ℝ) :
    (BasisData.rf85).eval (a-83/256)=(SourceBasis.rf85).eval a := by
  apply translated_rf_of_scaled (BasisData.rf85) (SourceBasis.rf85) (1/120:ℝ) (1/24:ℝ) a (83/256)
  · have hh := RFChecks.e85n.sound RFChecks.e85n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e85n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e85n.left 0)=integerCoefficients (BasisData.rf85).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e85n.target0=affineShift (SourceBasis.rf85).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf85).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(8646911284551352320:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf85).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(4222124650659840:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(8646911284551352320:ℤ)] (a-(83/256:ℝ))=(8646911284551352320:ℝ) by simp [evalZ,horner]),(show evalZ [(4222124650659840:ℤ)] (a-(83/256:ℝ))=(4222124650659840:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf85] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf85).numerator.denominator = 4222124650659840 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf85).numerator) (a-(83/256:ℝ)) /
      (4222124650659840:ℝ) = (1/120:ℝ)*evalZ (SourceBasis.rf85).numerator a
    simp only [SourceBasis.rf85]
    nlinarith [hh]
  · have hh := RFChecks.e85d.sound RFChecks.e85d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e85d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e85d.left 0)=factorCoefficients (BasisData.rf85).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e85d.target0=affineShift (SourceBasis.rf85).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf85).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(26388279066624:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf85).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(26388279066624:ℤ)] (a-(83/256:ℝ))=(26388279066624:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf85] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf85).factors = 4294967296 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf85).factors) (a-(83/256:ℝ)) /
      (4294967296:ℝ) = (1/24:ℝ)*evalZ (SourceBasis.rf85).denominator a
    simp only [SourceBasis.rf85]
    nlinarith [hh]
  · norm_num [BasisData.rf85,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf86_translation (a : ℝ) :
    (BasisData.rf86).eval (a-83/256)=(SourceBasis.rf86).eval a := by
  apply translated_rf_of_scaled (BasisData.rf86) (SourceBasis.rf86) (1/240:ℝ) (1/48:ℝ) a (83/256)
  · have hh := RFChecks.e86n.sound RFChecks.e86n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e86n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e86n.left 0)=integerCoefficients (BasisData.rf86).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e86n.target0=affineShift (SourceBasis.rf86).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf86).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(4427218577690292387840:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf86).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(17293822569102704640:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(4427218577690292387840:ℤ)] (a-(83/256:ℝ))=(4427218577690292387840:ℝ) by simp [evalZ,horner]),(show evalZ [(17293822569102704640:ℤ)] (a-(83/256:ℝ))=(17293822569102704640:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf86] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf86).numerator.denominator = 17293822569102704640 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf86).numerator) (a-(83/256:ℝ)) /
      (17293822569102704640:ℝ) = (1/240:ℝ)*evalZ (SourceBasis.rf86).numerator a
    simp only [SourceBasis.rf86]
    nlinarith [hh]
  · have hh := RFChecks.e86d.sound RFChecks.e86d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e86d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e86d.left 0)=factorCoefficients (BasisData.rf86).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e86d.target0=affineShift (SourceBasis.rf86).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf86).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(52776558133248:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf86).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(52776558133248:ℤ)] (a-(83/256:ℝ))=(52776558133248:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf86] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf86).factors = 4294967296 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf86).factors) (a-(83/256:ℝ)) /
      (4294967296:ℝ) = (1/48:ℝ)*evalZ (SourceBasis.rf86).denominator a
    simp only [SourceBasis.rf86]
    nlinarith [hh]
  · norm_num [BasisData.rf86,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf87_translation (a : ℝ) :
    (BasisData.rf87).eval (a-83/256)=(SourceBasis.rf87).eval a := by
  apply translated_rf_of_scaled (BasisData.rf87) (SourceBasis.rf87) (1/120:ℝ) (1/24:ℝ) a (83/256)
  · have hh := RFChecks.e87n.sound RFChecks.e87n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e87n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e87n.left 0)=integerCoefficients (BasisData.rf87).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e87n.target0=affineShift (SourceBasis.rf87).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf87).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2213609288845146193920:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf87).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(540431955284459520:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2213609288845146193920:ℤ)] (a-(83/256:ℝ))=(2213609288845146193920:ℝ) by simp [evalZ,horner]),(show evalZ [(540431955284459520:ℤ)] (a-(83/256:ℝ))=(540431955284459520:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf87] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf87).numerator.denominator = 540431955284459520 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf87).numerator) (a-(83/256:ℝ)) /
      (540431955284459520:ℝ) = (1/120:ℝ)*evalZ (SourceBasis.rf87).numerator a
    simp only [SourceBasis.rf87]
    nlinarith [hh]
  · have hh := RFChecks.e87d.sound RFChecks.e87d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e87d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e87d.left 0)=factorCoefficients (BasisData.rf87).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e87d.target0=affineShift (SourceBasis.rf87).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf87).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(26388279066624:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf87).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(26388279066624:ℤ)] (a-(83/256:ℝ))=(26388279066624:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf87] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf87).factors = 4294967296 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf87).factors) (a-(83/256:ℝ)) /
      (4294967296:ℝ) = (1/24:ℝ)*evalZ (SourceBasis.rf87).denominator a
    simp only [SourceBasis.rf87]
    nlinarith [hh]
  · norm_num [BasisData.rf87,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf88_translation (a : ℝ) :
    (BasisData.rf88).eval (a-83/256)=(SourceBasis.rf88).eval a := by
  apply translated_rf_of_scaled (BasisData.rf88) (SourceBasis.rf88) (1/120:ℝ) (1/24:ℝ) a (83/256)
  · have hh := RFChecks.e88n.sound RFChecks.e88n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e88n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e88n.left 0)=integerCoefficients (BasisData.rf88).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e88n.target0=affineShift (SourceBasis.rf88).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf88).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2213609288845146193920:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf88).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(1080863910568919040:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2213609288845146193920:ℤ)] (a-(83/256:ℝ))=(2213609288845146193920:ℝ) by simp [evalZ,horner]),(show evalZ [(1080863910568919040:ℤ)] (a-(83/256:ℝ))=(1080863910568919040:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf88] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf88).numerator.denominator = 1080863910568919040 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf88).numerator) (a-(83/256:ℝ)) /
      (1080863910568919040:ℝ) = (1/120:ℝ)*evalZ (SourceBasis.rf88).numerator a
    simp only [SourceBasis.rf88]
    nlinarith [hh]
  · have hh := RFChecks.e88d.sound RFChecks.e88d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e88d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e88d.left 0)=factorCoefficients (BasisData.rf88).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e88d.target0=affineShift (SourceBasis.rf88).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf88).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(26388279066624:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf88).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(26388279066624:ℤ)] (a-(83/256:ℝ))=(26388279066624:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf88] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf88).factors = 4294967296 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf88).factors) (a-(83/256:ℝ)) /
      (4294967296:ℝ) = (1/24:ℝ)*evalZ (SourceBasis.rf88).denominator a
    simp only [SourceBasis.rf88]
    nlinarith [hh]
  · norm_num [BasisData.rf88,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf89_translation (a : ℝ) :
    (BasisData.rf89).eval (a-83/256)=(SourceBasis.rf89).eval a := by
  apply translated_rf_of_scaled (BasisData.rf89) (SourceBasis.rf89) (1/3:ℝ) (1/3:ℝ) a (83/256)
  · have hh := RFChecks.e89n.sound RFChecks.e89n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e89n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e89n.left 0)=integerCoefficients (BasisData.rf89).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e89n.target0=affineShift (SourceBasis.rf89).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf89).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(3298534883328:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf89).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(6442450944:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(3298534883328:ℤ)] (a-(83/256:ℝ))=(3298534883328:ℝ) by simp [evalZ,horner]),(show evalZ [(6442450944:ℤ)] (a-(83/256:ℝ))=(6442450944:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf89] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf89).numerator.denominator = 6442450944 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf89).numerator) (a-(83/256:ℝ)) /
      (6442450944:ℝ) = (1/3:ℝ)*evalZ (SourceBasis.rf89).numerator a
    simp only [SourceBasis.rf89]
    nlinarith [hh]
  · have hh := RFChecks.e89d.sound RFChecks.e89d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e89d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e89d.left 0)=factorCoefficients (BasisData.rf89).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e89d.target0=affineShift (SourceBasis.rf89).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf89).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(196608:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf89).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(256:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(196608:ℤ)] (a-(83/256:ℝ))=(196608:ℝ) by simp [evalZ,horner]),(show evalZ [(256:ℤ)] (a-(83/256:ℝ))=(256:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf89] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf89).factors = 256 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf89).factors) (a-(83/256:ℝ)) /
      (256:ℝ) = (1/3:ℝ)*evalZ (SourceBasis.rf89).denominator a
    simp only [SourceBasis.rf89]
    nlinarith [hh]
  · norm_num [BasisData.rf89,ThomsonNegative.Compact.Packed.qval]
  · norm_num

#print axioms rf80_translation
end ThomsonNegative.Certificate.Bridges
