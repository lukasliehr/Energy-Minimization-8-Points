import ThomsonNegative.Certificate.Bridges.RFChecks09
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
theorem rf90_translation (a : ℝ) :
    (BasisData.rf90).eval (a-83/256)=(SourceBasis.rf90).eval a := by
  apply translated_rf_of_scaled (BasisData.rf90) (SourceBasis.rf90) (1/360:ℝ) (1/72:ℝ) a (83/256)
  · have hh := RFChecks.e90n.sound RFChecks.e90n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e90n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e90n.left 0)=integerCoefficients (BasisData.rf90).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e90n.target0=affineShift (SourceBasis.rf90).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf90).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(25940733853654056960:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf90).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(101330991615836160:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(25940733853654056960:ℤ)] (a-(83/256:ℝ))=(25940733853654056960:ℝ) by simp [evalZ,horner]),(show evalZ [(101330991615836160:ℤ)] (a-(83/256:ℝ))=(101330991615836160:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf90] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf90).numerator.denominator = 101330991615836160 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf90).numerator) (a-(83/256:ℝ)) /
      (101330991615836160:ℝ) = (1/360:ℝ)*evalZ (SourceBasis.rf90).numerator a
    simp only [SourceBasis.rf90]
    nlinarith [hh]
  · have hh := RFChecks.e90d.sound RFChecks.e90d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e90d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e90d.left 0)=factorCoefficients (BasisData.rf90).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e90d.target0=affineShift (SourceBasis.rf90).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf90).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(79164837199872:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf90).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(79164837199872:ℤ)] (a-(83/256:ℝ))=(79164837199872:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf90] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf90).factors = 4294967296 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf90).factors) (a-(83/256:ℝ)) /
      (4294967296:ℝ) = (1/72:ℝ)*evalZ (SourceBasis.rf90).denominator a
    simp only [SourceBasis.rf90]
    nlinarith [hh]
  · norm_num [BasisData.rf90,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf91_translation (a : ℝ) :
    (BasisData.rf91).eval (a-83/256)=(SourceBasis.rf91).eval a := by
  apply translated_rf_of_scaled (BasisData.rf91) (SourceBasis.rf91) (1/360:ℝ) (1/72:ℝ) a (83/256)
  · have hh := RFChecks.e91n.sound RFChecks.e91n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e91n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e91n.left 0)=integerCoefficients (BasisData.rf91).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e91n.target0=affineShift (SourceBasis.rf91).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf91).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(6640827866535438581760:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf91).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(12970366926827028480:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(6640827866535438581760:ℤ)] (a-(83/256:ℝ))=(6640827866535438581760:ℝ) by simp [evalZ,horner]),(show evalZ [(12970366926827028480:ℤ)] (a-(83/256:ℝ))=(12970366926827028480:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf91] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf91).numerator.denominator = 12970366926827028480 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf91).numerator) (a-(83/256:ℝ)) /
      (12970366926827028480:ℝ) = (1/360:ℝ)*evalZ (SourceBasis.rf91).numerator a
    simp only [SourceBasis.rf91]
    nlinarith [hh]
  · have hh := RFChecks.e91d.sound RFChecks.e91d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e91d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e91d.left 0)=factorCoefficients (BasisData.rf91).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e91d.target0=affineShift (SourceBasis.rf91).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf91).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(79164837199872:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf91).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(79164837199872:ℤ)] (a-(83/256:ℝ))=(79164837199872:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf91] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf91).factors = 4294967296 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf91).factors) (a-(83/256:ℝ)) /
      (4294967296:ℝ) = (1/72:ℝ)*evalZ (SourceBasis.rf91).denominator a
    simp only [SourceBasis.rf91]
    nlinarith [hh]
  · norm_num [BasisData.rf91,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf92_translation (a : ℝ) :
    (BasisData.rf92).eval (a-83/256)=(SourceBasis.rf92).eval a := by
  apply translated_rf_of_scaled (BasisData.rf92) (SourceBasis.rf92) (1/360:ℝ) (1/72:ℝ) a (83/256)
  · have hh := RFChecks.e92n.sound RFChecks.e92n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e92n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e92n.left 0)=integerCoefficients (BasisData.rf92).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e92n.target0=affineShift (SourceBasis.rf92).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf92).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(6640827866535438581760:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf92).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(6485183463413514240:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(6640827866535438581760:ℤ)] (a-(83/256:ℝ))=(6640827866535438581760:ℝ) by simp [evalZ,horner]),(show evalZ [(6485183463413514240:ℤ)] (a-(83/256:ℝ))=(6485183463413514240:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf92] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf92).numerator.denominator = 6485183463413514240 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf92).numerator) (a-(83/256:ℝ)) /
      (6485183463413514240:ℝ) = (1/360:ℝ)*evalZ (SourceBasis.rf92).numerator a
    simp only [SourceBasis.rf92]
    nlinarith [hh]
  · have hh := RFChecks.e92d.sound RFChecks.e92d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e92d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e92d.left 0)=factorCoefficients (BasisData.rf92).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e92d.target0=affineShift (SourceBasis.rf92).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf92).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(79164837199872:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf92).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(79164837199872:ℤ)] (a-(83/256:ℝ))=(79164837199872:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf92] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf92).factors = 4294967296 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf92).factors) (a-(83/256:ℝ)) /
      (4294967296:ℝ) = (1/72:ℝ)*evalZ (SourceBasis.rf92).denominator a
    simp only [SourceBasis.rf92]
    nlinarith [hh]
  · norm_num [BasisData.rf92,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf93_translation (a : ℝ) :
    (BasisData.rf93).eval (a-83/256)=(SourceBasis.rf93).eval a := by
  apply translated_rf_of_scaled (BasisData.rf93) (SourceBasis.rf93) (1/9:ℝ) (1/9:ℝ) a (83/256)
  · have hh := RFChecks.e93n.sound RFChecks.e93n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e93n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e93n.left 0)=integerCoefficients (BasisData.rf93).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e93n.target0=affineShift (SourceBasis.rf93).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf93).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(9895604649984:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf93).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(38654705664:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(9895604649984:ℤ)] (a-(83/256:ℝ))=(9895604649984:ℝ) by simp [evalZ,horner]),(show evalZ [(38654705664:ℤ)] (a-(83/256:ℝ))=(38654705664:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf93] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf93).numerator.denominator = 38654705664 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf93).numerator) (a-(83/256:ℝ)) /
      (38654705664:ℝ) = (1/9:ℝ)*evalZ (SourceBasis.rf93).numerator a
    simp only [SourceBasis.rf93]
    nlinarith [hh]
  · have hh := RFChecks.e93d.sound RFChecks.e93d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e93d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e93d.left 0)=factorCoefficients (BasisData.rf93).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e93d.target0=affineShift (SourceBasis.rf93).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf93).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(589824:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf93).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(256:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(589824:ℤ)] (a-(83/256:ℝ))=(589824:ℝ) by simp [evalZ,horner]),(show evalZ [(256:ℤ)] (a-(83/256:ℝ))=(256:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf93] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf93).factors = 256 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf93).factors) (a-(83/256:ℝ)) /
      (256:ℝ) = (1/9:ℝ)*evalZ (SourceBasis.rf93).denominator a
    simp only [SourceBasis.rf93]
    nlinarith [hh]
  · norm_num [BasisData.rf93,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf94_translation (a : ℝ) :
    (BasisData.rf94).eval (a-83/256)=(SourceBasis.rf94).eval a := by
  apply translated_rf_of_scaled (BasisData.rf94) (SourceBasis.rf94) (1/120:ℝ) (1/24:ℝ) a (83/256)
  · have hh := RFChecks.e94n.sound RFChecks.e94n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e94n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e94n.left 0)=integerCoefficients (BasisData.rf94).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e94n.target0=affineShift (SourceBasis.rf94).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf94).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(33776997205278720:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf94).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(65970697666560:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(33776997205278720:ℤ)] (a-(83/256:ℝ))=(33776997205278720:ℝ) by simp [evalZ,horner]),(show evalZ [(65970697666560:ℤ)] (a-(83/256:ℝ))=(65970697666560:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf94] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf94).numerator.denominator = 65970697666560 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf94).numerator) (a-(83/256:ℝ)) /
      (65970697666560:ℝ) = (1/120:ℝ)*evalZ (SourceBasis.rf94).numerator a
    simp only [SourceBasis.rf94]
    nlinarith [hh]
  · have hh := RFChecks.e94d.sound RFChecks.e94d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e94d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e94d.left 0)=factorCoefficients (BasisData.rf94).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e94d.target0=affineShift (SourceBasis.rf94).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf94).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(6755399441055744:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf94).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(6755399441055744:ℤ)] (a-(83/256:ℝ))=(6755399441055744:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf94] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf94).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf94).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/24:ℝ)*evalZ (SourceBasis.rf94).denominator a
    simp only [SourceBasis.rf94]
    nlinarith [hh]
  · norm_num [BasisData.rf94,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf95_translation (a : ℝ) :
    (BasisData.rf95).eval (a-83/256)=(SourceBasis.rf95).eval a := by
  apply translated_rf_of_scaled (BasisData.rf95) (SourceBasis.rf95) (1/120:ℝ) (1/24:ℝ) a (83/256)
  · have hh := RFChecks.e95n.sound RFChecks.e95n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e95n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e95n.left 0)=integerCoefficients (BasisData.rf95).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e95n.target0=affineShift (SourceBasis.rf95).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf95).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(8646911284551352320:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf95).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(1055531162664960:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(8646911284551352320:ℤ)] (a-(83/256:ℝ))=(8646911284551352320:ℝ) by simp [evalZ,horner]),(show evalZ [(1055531162664960:ℤ)] (a-(83/256:ℝ))=(1055531162664960:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf95] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf95).numerator.denominator = 1055531162664960 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf95).numerator) (a-(83/256:ℝ)) /
      (1055531162664960:ℝ) = (1/120:ℝ)*evalZ (SourceBasis.rf95).numerator a
    simp only [SourceBasis.rf95]
    nlinarith [hh]
  · have hh := RFChecks.e95d.sound RFChecks.e95d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e95d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e95d.left 0)=factorCoefficients (BasisData.rf95).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e95d.target0=affineShift (SourceBasis.rf95).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf95).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(6755399441055744:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf95).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(6755399441055744:ℤ)] (a-(83/256:ℝ))=(6755399441055744:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf95] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf95).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf95).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/24:ℝ)*evalZ (SourceBasis.rf95).denominator a
    simp only [SourceBasis.rf95]
    nlinarith [hh]
  · norm_num [BasisData.rf95,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf96_translation (a : ℝ) :
    (BasisData.rf96).eval (a-83/256)=(SourceBasis.rf96).eval a := by
  apply translated_rf_of_scaled (BasisData.rf96) (SourceBasis.rf96) (1/120:ℝ) (1/24:ℝ) a (83/256)
  · have hh := RFChecks.e96n.sound RFChecks.e96n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e96n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e96n.left 0)=integerCoefficients (BasisData.rf96).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e96n.target0=affineShift (SourceBasis.rf96).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf96).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(8646911284551352320:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf96).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(4222124650659840:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(8646911284551352320:ℤ)] (a-(83/256:ℝ))=(8646911284551352320:ℝ) by simp [evalZ,horner]),(show evalZ [(4222124650659840:ℤ)] (a-(83/256:ℝ))=(4222124650659840:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf96] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf96).numerator.denominator = 4222124650659840 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf96).numerator) (a-(83/256:ℝ)) /
      (4222124650659840:ℝ) = (1/120:ℝ)*evalZ (SourceBasis.rf96).numerator a
    simp only [SourceBasis.rf96]
    nlinarith [hh]
  · have hh := RFChecks.e96d.sound RFChecks.e96d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e96d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e96d.left 0)=factorCoefficients (BasisData.rf96).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e96d.target0=affineShift (SourceBasis.rf96).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf96).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(6755399441055744:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf96).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(6755399441055744:ℤ)] (a-(83/256:ℝ))=(6755399441055744:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf96] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf96).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf96).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/24:ℝ)*evalZ (SourceBasis.rf96).denominator a
    simp only [SourceBasis.rf96]
    nlinarith [hh]
  · norm_num [BasisData.rf96,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf97_translation (a : ℝ) :
    (BasisData.rf97).eval (a-83/256)=(SourceBasis.rf97).eval a := by
  apply translated_rf_of_scaled (BasisData.rf97) (SourceBasis.rf97) (1/240:ℝ) (1/48:ℝ) a (83/256)
  · have hh := RFChecks.e97n.sound RFChecks.e97n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e97n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e97n.left 0)=integerCoefficients (BasisData.rf97).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e97n.target0=affineShift (SourceBasis.rf97).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf97).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(4427218577690292387840:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf97).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(8646911284551352320:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(4427218577690292387840:ℤ)] (a-(83/256:ℝ))=(4427218577690292387840:ℝ) by simp [evalZ,horner]),(show evalZ [(8646911284551352320:ℤ)] (a-(83/256:ℝ))=(8646911284551352320:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf97] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf97).numerator.denominator = 8646911284551352320 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf97).numerator) (a-(83/256:ℝ)) /
      (8646911284551352320:ℝ) = (1/240:ℝ)*evalZ (SourceBasis.rf97).numerator a
    simp only [SourceBasis.rf97]
    nlinarith [hh]
  · have hh := RFChecks.e97d.sound RFChecks.e97d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e97d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e97d.left 0)=factorCoefficients (BasisData.rf97).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e97d.target0=affineShift (SourceBasis.rf97).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf97).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(13510798882111488:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf97).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(13510798882111488:ℤ)] (a-(83/256:ℝ))=(13510798882111488:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf97] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf97).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf97).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/48:ℝ)*evalZ (SourceBasis.rf97).denominator a
    simp only [SourceBasis.rf97]
    nlinarith [hh]
  · norm_num [BasisData.rf97,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf98_translation (a : ℝ) :
    (BasisData.rf98).eval (a-83/256)=(SourceBasis.rf98).eval a := by
  apply translated_rf_of_scaled (BasisData.rf98) (SourceBasis.rf98) (1/120:ℝ) (1/24:ℝ) a (83/256)
  · have hh := RFChecks.e98n.sound RFChecks.e98n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e98n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e98n.left 0)=integerCoefficients (BasisData.rf98).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e98n.target0=affineShift (SourceBasis.rf98).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf98).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2213609288845146193920:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf98).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(270215977642229760:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2213609288845146193920:ℤ)] (a-(83/256:ℝ))=(2213609288845146193920:ℝ) by simp [evalZ,horner]),(show evalZ [(270215977642229760:ℤ)] (a-(83/256:ℝ))=(270215977642229760:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf98] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf98).numerator.denominator = 270215977642229760 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf98).numerator) (a-(83/256:ℝ)) /
      (270215977642229760:ℝ) = (1/120:ℝ)*evalZ (SourceBasis.rf98).numerator a
    simp only [SourceBasis.rf98]
    nlinarith [hh]
  · have hh := RFChecks.e98d.sound RFChecks.e98d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e98d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e98d.left 0)=factorCoefficients (BasisData.rf98).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e98d.target0=affineShift (SourceBasis.rf98).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf98).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(6755399441055744:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf98).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(6755399441055744:ℤ)] (a-(83/256:ℝ))=(6755399441055744:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf98] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf98).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf98).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/24:ℝ)*evalZ (SourceBasis.rf98).denominator a
    simp only [SourceBasis.rf98]
    nlinarith [hh]
  · norm_num [BasisData.rf98,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf99_translation (a : ℝ) :
    (BasisData.rf99).eval (a-83/256)=(SourceBasis.rf99).eval a := by
  apply translated_rf_of_scaled (BasisData.rf99) (SourceBasis.rf99) (1/120:ℝ) (1/24:ℝ) a (83/256)
  · have hh := RFChecks.e99n.sound RFChecks.e99n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e99n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e99n.left 0)=integerCoefficients (BasisData.rf99).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e99n.target0=affineShift (SourceBasis.rf99).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf99).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2213609288845146193920:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf99).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(2161727821137838080:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2213609288845146193920:ℤ)] (a-(83/256:ℝ))=(2213609288845146193920:ℝ) by simp [evalZ,horner]),(show evalZ [(2161727821137838080:ℤ)] (a-(83/256:ℝ))=(2161727821137838080:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf99] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf99).numerator.denominator = 2161727821137838080 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf99).numerator) (a-(83/256:ℝ)) /
      (2161727821137838080:ℝ) = (1/120:ℝ)*evalZ (SourceBasis.rf99).numerator a
    simp only [SourceBasis.rf99]
    nlinarith [hh]
  · have hh := RFChecks.e99d.sound RFChecks.e99d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e99d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e99d.left 0)=factorCoefficients (BasisData.rf99).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e99d.target0=affineShift (SourceBasis.rf99).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf99).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(6755399441055744:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf99).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(6755399441055744:ℤ)] (a-(83/256:ℝ))=(6755399441055744:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf99] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf99).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf99).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/24:ℝ)*evalZ (SourceBasis.rf99).denominator a
    simp only [SourceBasis.rf99]
    nlinarith [hh]
  · norm_num [BasisData.rf99,ThomsonNegative.Compact.Packed.qval]
  · norm_num

#print axioms rf90_translation
end ThomsonNegative.Certificate.Bridges
