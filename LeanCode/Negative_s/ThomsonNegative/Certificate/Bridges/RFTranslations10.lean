import ThomsonNegative.Certificate.Bridges.RFChecks10
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
theorem rf100_translation (a : ℝ) :
    (BasisData.rf100).eval (a-83/256)=(SourceBasis.rf100).eval a := by
  apply translated_rf_of_scaled (BasisData.rf100) (SourceBasis.rf100) (1/3:ℝ) (1/3:ℝ) a (83/256)
  · have hh := RFChecks.e100n.sound RFChecks.e100n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e100n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e100n.left 0)=integerCoefficients (BasisData.rf100).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e100n.target0=affineShift (SourceBasis.rf100).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf100).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(12884901888:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf100).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(50331648:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(12884901888:ℤ)] (a-(83/256:ℝ))=(12884901888:ℝ) by simp [evalZ,horner]),(show evalZ [(50331648:ℤ)] (a-(83/256:ℝ))=(50331648:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf100] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf100).numerator.denominator = 50331648 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf100).numerator) (a-(83/256:ℝ)) /
      (50331648:ℝ) = (1/3:ℝ)*evalZ (SourceBasis.rf100).numerator a
    simp only [SourceBasis.rf100]
    nlinarith [hh]
  · have hh := RFChecks.e100d.sound RFChecks.e100d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e100d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e100d.left 0)=factorCoefficients (BasisData.rf100).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e100d.target0=affineShift (SourceBasis.rf100).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf100).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(196608:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf100).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(256:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(196608:ℤ)] (a-(83/256:ℝ))=(196608:ℝ) by simp [evalZ,horner]),(show evalZ [(256:ℤ)] (a-(83/256:ℝ))=(256:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf100] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf100).factors = 256 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf100).factors) (a-(83/256:ℝ)) /
      (256:ℝ) = (1/3:ℝ)*evalZ (SourceBasis.rf100).denominator a
    simp only [SourceBasis.rf100]
    nlinarith [hh]
  · norm_num [BasisData.rf100,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf101_translation (a : ℝ) :
    (BasisData.rf101).eval (a-83/256)=(SourceBasis.rf101).eval a := by
  apply translated_rf_of_scaled (BasisData.rf101) (SourceBasis.rf101) (1/360:ℝ) (1/72:ℝ) a (83/256)
  · have hh := RFChecks.e101n.sound RFChecks.e101n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e101n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e101n.left 0)=integerCoefficients (BasisData.rf101).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e101n.target0=affineShift (SourceBasis.rf101).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf101).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(25940733853654056960:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf101).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(50665495807918080:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(25940733853654056960:ℤ)] (a-(83/256:ℝ))=(25940733853654056960:ℝ) by simp [evalZ,horner]),(show evalZ [(50665495807918080:ℤ)] (a-(83/256:ℝ))=(50665495807918080:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf101] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf101).numerator.denominator = 50665495807918080 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf101).numerator) (a-(83/256:ℝ)) /
      (50665495807918080:ℝ) = (1/360:ℝ)*evalZ (SourceBasis.rf101).numerator a
    simp only [SourceBasis.rf101]
    nlinarith [hh]
  · have hh := RFChecks.e101d.sound RFChecks.e101d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e101d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e101d.left 0)=factorCoefficients (BasisData.rf101).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e101d.target0=affineShift (SourceBasis.rf101).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf101).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(20266198323167232:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf101).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(20266198323167232:ℤ)] (a-(83/256:ℝ))=(20266198323167232:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf101] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf101).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf101).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/72:ℝ)*evalZ (SourceBasis.rf101).denominator a
    simp only [SourceBasis.rf101]
    nlinarith [hh]
  · norm_num [BasisData.rf101,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf102_translation (a : ℝ) :
    (BasisData.rf102).eval (a-83/256)=(SourceBasis.rf102).eval a := by
  apply translated_rf_of_scaled (BasisData.rf102) (SourceBasis.rf102) (1/360:ℝ) (1/72:ℝ) a (83/256)
  · have hh := RFChecks.e102n.sound RFChecks.e102n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e102n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e102n.left 0)=integerCoefficients (BasisData.rf102).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e102n.target0=affineShift (SourceBasis.rf102).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf102).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(6640827866535438581760:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf102).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(6485183463413514240:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(6640827866535438581760:ℤ)] (a-(83/256:ℝ))=(6640827866535438581760:ℝ) by simp [evalZ,horner]),(show evalZ [(6485183463413514240:ℤ)] (a-(83/256:ℝ))=(6485183463413514240:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf102] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf102).numerator.denominator = 6485183463413514240 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf102).numerator) (a-(83/256:ℝ)) /
      (6485183463413514240:ℝ) = (1/360:ℝ)*evalZ (SourceBasis.rf102).numerator a
    simp only [SourceBasis.rf102]
    nlinarith [hh]
  · have hh := RFChecks.e102d.sound RFChecks.e102d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e102d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e102d.left 0)=factorCoefficients (BasisData.rf102).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e102d.target0=affineShift (SourceBasis.rf102).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf102).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(20266198323167232:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf102).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(20266198323167232:ℤ)] (a-(83/256:ℝ))=(20266198323167232:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf102] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf102).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf102).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/72:ℝ)*evalZ (SourceBasis.rf102).denominator a
    simp only [SourceBasis.rf102]
    nlinarith [hh]
  · norm_num [BasisData.rf102,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf103_translation (a : ℝ) :
    (BasisData.rf103).eval (a-83/256)=(SourceBasis.rf103).eval a := by
  apply translated_rf_of_scaled (BasisData.rf103) (SourceBasis.rf103) (1/360:ℝ) (1/72:ℝ) a (83/256)
  · have hh := RFChecks.e103n.sound RFChecks.e103n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e103n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e103n.left 0)=integerCoefficients (BasisData.rf103).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e103n.target0=affineShift (SourceBasis.rf103).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf103).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(6640827866535438581760:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf103).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(6485183463413514240:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(6640827866535438581760:ℤ)] (a-(83/256:ℝ))=(6640827866535438581760:ℝ) by simp [evalZ,horner]),(show evalZ [(6485183463413514240:ℤ)] (a-(83/256:ℝ))=(6485183463413514240:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf103] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf103).numerator.denominator = 6485183463413514240 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf103).numerator) (a-(83/256:ℝ)) /
      (6485183463413514240:ℝ) = (1/360:ℝ)*evalZ (SourceBasis.rf103).numerator a
    simp only [SourceBasis.rf103]
    nlinarith [hh]
  · have hh := RFChecks.e103d.sound RFChecks.e103d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e103d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e103d.left 0)=factorCoefficients (BasisData.rf103).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e103d.target0=affineShift (SourceBasis.rf103).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf103).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(20266198323167232:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf103).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(20266198323167232:ℤ)] (a-(83/256:ℝ))=(20266198323167232:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf103] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf103).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf103).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/72:ℝ)*evalZ (SourceBasis.rf103).denominator a
    simp only [SourceBasis.rf103]
    nlinarith [hh]
  · norm_num [BasisData.rf103,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf104_translation (a : ℝ) :
    (BasisData.rf104).eval (a-83/256)=(SourceBasis.rf104).eval a := by
  apply translated_rf_of_scaled (BasisData.rf104) (SourceBasis.rf104) (1/9:ℝ) (1/9:ℝ) a (83/256)
  · have hh := RFChecks.e104n.sound RFChecks.e104n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e104n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e104n.left 0)=integerCoefficients (BasisData.rf104).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e104n.target0=affineShift (SourceBasis.rf104).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf104).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(38654705664:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf104).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(150994944:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(38654705664:ℤ)] (a-(83/256:ℝ))=(38654705664:ℝ) by simp [evalZ,horner]),(show evalZ [(150994944:ℤ)] (a-(83/256:ℝ))=(150994944:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf104] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf104).numerator.denominator = 150994944 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf104).numerator) (a-(83/256:ℝ)) /
      (150994944:ℝ) = (1/9:ℝ)*evalZ (SourceBasis.rf104).numerator a
    simp only [SourceBasis.rf104]
    nlinarith [hh]
  · have hh := RFChecks.e104d.sound RFChecks.e104d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e104d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e104d.left 0)=factorCoefficients (BasisData.rf104).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e104d.target0=affineShift (SourceBasis.rf104).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf104).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(589824:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf104).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(256:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(589824:ℤ)] (a-(83/256:ℝ))=(589824:ℝ) by simp [evalZ,horner]),(show evalZ [(256:ℤ)] (a-(83/256:ℝ))=(256:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf104] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf104).factors = 256 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf104).factors) (a-(83/256:ℝ)) /
      (256:ℝ) = (1/9:ℝ)*evalZ (SourceBasis.rf104).denominator a
    simp only [SourceBasis.rf104]
    nlinarith [hh]
  · norm_num [BasisData.rf104,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf105_translation (a : ℝ) :
    (BasisData.rf105).eval (a-83/256)=(SourceBasis.rf105).eval a := by
  apply translated_rf_of_scaled (BasisData.rf105) (SourceBasis.rf105) (1/120:ℝ) (1/24:ℝ) a (83/256)
  · have hh := RFChecks.e105n.sound RFChecks.e105n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e105n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e105n.left 0)=integerCoefficients (BasisData.rf105).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e105n.target0=affineShift (SourceBasis.rf105).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf105).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(131941395333120:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf105).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(515396075520:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(131941395333120:ℤ)] (a-(83/256:ℝ))=(131941395333120:ℝ) by simp [evalZ,horner]),(show evalZ [(515396075520:ℤ)] (a-(83/256:ℝ))=(515396075520:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf105] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf105).numerator.denominator = 515396075520 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf105).numerator) (a-(83/256:ℝ)) /
      (515396075520:ℝ) = (1/120:ℝ)*evalZ (SourceBasis.rf105).numerator a
    simp only [SourceBasis.rf105]
    nlinarith [hh]
  · have hh := RFChecks.e105d.sound RFChecks.e105d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e105d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e105d.left 0)=factorCoefficients (BasisData.rf105).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e105d.target0=affineShift (SourceBasis.rf105).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf105).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(6755399441055744:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf105).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(6755399441055744:ℤ)] (a-(83/256:ℝ))=(6755399441055744:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf105] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf105).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf105).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/24:ℝ)*evalZ (SourceBasis.rf105).denominator a
    simp only [SourceBasis.rf105]
    nlinarith [hh]
  · norm_num [BasisData.rf105,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf106_translation (a : ℝ) :
    (BasisData.rf106).eval (a-83/256)=(SourceBasis.rf106).eval a := by
  apply translated_rf_of_scaled (BasisData.rf106) (SourceBasis.rf106) (1/120:ℝ) (1/24:ℝ) a (83/256)
  · have hh := RFChecks.e106n.sound RFChecks.e106n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e106n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e106n.left 0)=integerCoefficients (BasisData.rf106).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e106n.target0=affineShift (SourceBasis.rf106).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf106).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(33776997205278720:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf106).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(65970697666560:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(33776997205278720:ℤ)] (a-(83/256:ℝ))=(33776997205278720:ℝ) by simp [evalZ,horner]),(show evalZ [(65970697666560:ℤ)] (a-(83/256:ℝ))=(65970697666560:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf106] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf106).numerator.denominator = 65970697666560 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf106).numerator) (a-(83/256:ℝ)) /
      (65970697666560:ℝ) = (1/120:ℝ)*evalZ (SourceBasis.rf106).numerator a
    simp only [SourceBasis.rf106]
    nlinarith [hh]
  · have hh := RFChecks.e106d.sound RFChecks.e106d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e106d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e106d.left 0)=factorCoefficients (BasisData.rf106).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e106d.target0=affineShift (SourceBasis.rf106).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf106).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(6755399441055744:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf106).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(6755399441055744:ℤ)] (a-(83/256:ℝ))=(6755399441055744:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf106] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf106).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf106).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/24:ℝ)*evalZ (SourceBasis.rf106).denominator a
    simp only [SourceBasis.rf106]
    nlinarith [hh]
  · norm_num [BasisData.rf106,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf107_translation (a : ℝ) :
    (BasisData.rf107).eval (a-83/256)=(SourceBasis.rf107).eval a := by
  apply translated_rf_of_scaled (BasisData.rf107) (SourceBasis.rf107) (1/120:ℝ) (1/24:ℝ) a (83/256)
  · have hh := RFChecks.e107n.sound RFChecks.e107n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e107n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e107n.left 0)=integerCoefficients (BasisData.rf107).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e107n.target0=affineShift (SourceBasis.rf107).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf107).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(33776997205278720:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf107).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(32985348833280:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(33776997205278720:ℤ)] (a-(83/256:ℝ))=(33776997205278720:ℝ) by simp [evalZ,horner]),(show evalZ [(32985348833280:ℤ)] (a-(83/256:ℝ))=(32985348833280:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf107] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf107).numerator.denominator = 32985348833280 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf107).numerator) (a-(83/256:ℝ)) /
      (32985348833280:ℝ) = (1/120:ℝ)*evalZ (SourceBasis.rf107).numerator a
    simp only [SourceBasis.rf107]
    nlinarith [hh]
  · have hh := RFChecks.e107d.sound RFChecks.e107d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e107d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e107d.left 0)=factorCoefficients (BasisData.rf107).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e107d.target0=affineShift (SourceBasis.rf107).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf107).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(6755399441055744:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf107).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(6755399441055744:ℤ)] (a-(83/256:ℝ))=(6755399441055744:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf107] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf107).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf107).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/24:ℝ)*evalZ (SourceBasis.rf107).denominator a
    simp only [SourceBasis.rf107]
    nlinarith [hh]
  · norm_num [BasisData.rf107,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf108_translation (a : ℝ) :
    (BasisData.rf108).eval (a-83/256)=(SourceBasis.rf108).eval a := by
  apply translated_rf_of_scaled (BasisData.rf108) (SourceBasis.rf108) (1/240:ℝ) (1/48:ℝ) a (83/256)
  · have hh := RFChecks.e108n.sound RFChecks.e108n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e108n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e108n.left 0)=integerCoefficients (BasisData.rf108).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e108n.target0=affineShift (SourceBasis.rf108).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf108).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(17293822569102704640:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf108).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(67553994410557440:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(17293822569102704640:ℤ)] (a-(83/256:ℝ))=(17293822569102704640:ℝ) by simp [evalZ,horner]),(show evalZ [(67553994410557440:ℤ)] (a-(83/256:ℝ))=(67553994410557440:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf108] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf108).numerator.denominator = 67553994410557440 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf108).numerator) (a-(83/256:ℝ)) /
      (67553994410557440:ℝ) = (1/240:ℝ)*evalZ (SourceBasis.rf108).numerator a
    simp only [SourceBasis.rf108]
    nlinarith [hh]
  · have hh := RFChecks.e108d.sound RFChecks.e108d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e108d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e108d.left 0)=factorCoefficients (BasisData.rf108).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e108d.target0=affineShift (SourceBasis.rf108).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf108).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(13510798882111488:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf108).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(13510798882111488:ℤ)] (a-(83/256:ℝ))=(13510798882111488:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf108] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf108).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf108).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/48:ℝ)*evalZ (SourceBasis.rf108).denominator a
    simp only [SourceBasis.rf108]
    nlinarith [hh]
  · norm_num [BasisData.rf108,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf109_translation (a : ℝ) :
    (BasisData.rf109).eval (a-83/256)=(SourceBasis.rf109).eval a := by
  apply translated_rf_of_scaled (BasisData.rf109) (SourceBasis.rf109) (1/120:ℝ) (1/24:ℝ) a (83/256)
  · have hh := RFChecks.e109n.sound RFChecks.e109n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e109n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e109n.left 0)=integerCoefficients (BasisData.rf109).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e109n.target0=affineShift (SourceBasis.rf109).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf109).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(8646911284551352320:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf109).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(8444249301319680:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(8646911284551352320:ℤ)] (a-(83/256:ℝ))=(8646911284551352320:ℝ) by simp [evalZ,horner]),(show evalZ [(8444249301319680:ℤ)] (a-(83/256:ℝ))=(8444249301319680:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf109] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf109).numerator.denominator = 8444249301319680 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf109).numerator) (a-(83/256:ℝ)) /
      (8444249301319680:ℝ) = (1/120:ℝ)*evalZ (SourceBasis.rf109).numerator a
    simp only [SourceBasis.rf109]
    nlinarith [hh]
  · have hh := RFChecks.e109d.sound RFChecks.e109d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e109d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e109d.left 0)=factorCoefficients (BasisData.rf109).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e109d.target0=affineShift (SourceBasis.rf109).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf109).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(6755399441055744:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf109).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(6755399441055744:ℤ)] (a-(83/256:ℝ))=(6755399441055744:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf109] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf109).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf109).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/24:ℝ)*evalZ (SourceBasis.rf109).denominator a
    simp only [SourceBasis.rf109]
    nlinarith [hh]
  · norm_num [BasisData.rf109,ThomsonNegative.Compact.Packed.qval]
  · norm_num

#print axioms rf100_translation
end ThomsonNegative.Certificate.Bridges
