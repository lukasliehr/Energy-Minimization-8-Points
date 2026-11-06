import ThomsonNegative.Certificate.Bridges.RFChecks11
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
theorem rf110_translation (a : ℝ) :
    (BasisData.rf110).eval (a-83/256)=(SourceBasis.rf110).eval a := by
  apply translated_rf_of_scaled (BasisData.rf110) (SourceBasis.rf110) (1/120:ℝ) (1/24:ℝ) a (83/256)
  · have hh := RFChecks.e110n.sound RFChecks.e110n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e110n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e110n.left 0)=integerCoefficients (BasisData.rf110).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e110n.target0=affineShift (SourceBasis.rf110).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf110).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(8646911284551352320:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf110).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(2111062325329920:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(8646911284551352320:ℤ)] (a-(83/256:ℝ))=(8646911284551352320:ℝ) by simp [evalZ,horner]),(show evalZ [(2111062325329920:ℤ)] (a-(83/256:ℝ))=(2111062325329920:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf110] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf110).numerator.denominator = 2111062325329920 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf110).numerator) (a-(83/256:ℝ)) /
      (2111062325329920:ℝ) = (1/120:ℝ)*evalZ (SourceBasis.rf110).numerator a
    simp only [SourceBasis.rf110]
    nlinarith [hh]
  · have hh := RFChecks.e110d.sound RFChecks.e110d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e110d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e110d.left 0)=factorCoefficients (BasisData.rf110).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e110d.target0=affineShift (SourceBasis.rf110).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf110).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(6755399441055744:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf110).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(6755399441055744:ℤ)] (a-(83/256:ℝ))=(6755399441055744:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf110] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf110).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf110).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/24:ℝ)*evalZ (SourceBasis.rf110).denominator a
    simp only [SourceBasis.rf110]
    nlinarith [hh]
  · norm_num [BasisData.rf110,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf111_translation (a : ℝ) :
    (BasisData.rf111).eval (a-83/256)=(SourceBasis.rf111).eval a := by
  apply translated_rf_of_scaled (BasisData.rf111) (SourceBasis.rf111) (1/3:ℝ) (1/3:ℝ) a (83/256)
  · have hh := RFChecks.e111n.sound RFChecks.e111n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e111n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e111n.left 0)=integerCoefficients (BasisData.rf111).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e111n.target0=affineShift (SourceBasis.rf111).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf111).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(50331648:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf111).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(98304:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(50331648:ℤ)] (a-(83/256:ℝ))=(50331648:ℝ) by simp [evalZ,horner]),(show evalZ [(98304:ℤ)] (a-(83/256:ℝ))=(98304:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf111] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf111).numerator.denominator = 98304 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf111).numerator) (a-(83/256:ℝ)) /
      (98304:ℝ) = (1/3:ℝ)*evalZ (SourceBasis.rf111).numerator a
    simp only [SourceBasis.rf111]
    nlinarith [hh]
  · have hh := RFChecks.e111d.sound RFChecks.e111d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e111d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e111d.left 0)=factorCoefficients (BasisData.rf111).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e111d.target0=affineShift (SourceBasis.rf111).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf111).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(196608:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf111).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(256:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(196608:ℤ)] (a-(83/256:ℝ))=(196608:ℝ) by simp [evalZ,horner]),(show evalZ [(256:ℤ)] (a-(83/256:ℝ))=(256:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf111] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf111).factors = 256 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf111).factors) (a-(83/256:ℝ)) /
      (256:ℝ) = (1/3:ℝ)*evalZ (SourceBasis.rf111).denominator a
    simp only [SourceBasis.rf111]
    nlinarith [hh]
  · norm_num [BasisData.rf111,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf112_translation (a : ℝ) :
    (BasisData.rf112).eval (a-83/256)=(SourceBasis.rf112).eval a := by
  apply translated_rf_of_scaled (BasisData.rf112) (SourceBasis.rf112) (1/360:ℝ) (1/72:ℝ) a (83/256)
  · have hh := RFChecks.e112n.sound RFChecks.e112n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e112n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e112n.left 0)=integerCoefficients (BasisData.rf112).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e112n.target0=affineShift (SourceBasis.rf112).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf112).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(101330991615836160:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf112).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(395824185999360:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(101330991615836160:ℤ)] (a-(83/256:ℝ))=(101330991615836160:ℝ) by simp [evalZ,horner]),(show evalZ [(395824185999360:ℤ)] (a-(83/256:ℝ))=(395824185999360:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf112] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf112).numerator.denominator = 395824185999360 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf112).numerator) (a-(83/256:ℝ)) /
      (395824185999360:ℝ) = (1/360:ℝ)*evalZ (SourceBasis.rf112).numerator a
    simp only [SourceBasis.rf112]
    nlinarith [hh]
  · have hh := RFChecks.e112d.sound RFChecks.e112d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e112d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e112d.left 0)=factorCoefficients (BasisData.rf112).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e112d.target0=affineShift (SourceBasis.rf112).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf112).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(20266198323167232:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf112).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(20266198323167232:ℤ)] (a-(83/256:ℝ))=(20266198323167232:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf112] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf112).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf112).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/72:ℝ)*evalZ (SourceBasis.rf112).denominator a
    simp only [SourceBasis.rf112]
    nlinarith [hh]
  · norm_num [BasisData.rf112,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf113_translation (a : ℝ) :
    (BasisData.rf113).eval (a-83/256)=(SourceBasis.rf113).eval a := by
  apply translated_rf_of_scaled (BasisData.rf113) (SourceBasis.rf113) (1/360:ℝ) (1/72:ℝ) a (83/256)
  · have hh := RFChecks.e113n.sound RFChecks.e113n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e113n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e113n.left 0)=integerCoefficients (BasisData.rf113).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e113n.target0=affineShift (SourceBasis.rf113).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf113).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(25940733853654056960:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf113).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(50665495807918080:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(25940733853654056960:ℤ)] (a-(83/256:ℝ))=(25940733853654056960:ℝ) by simp [evalZ,horner]),(show evalZ [(50665495807918080:ℤ)] (a-(83/256:ℝ))=(50665495807918080:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf113] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf113).numerator.denominator = 50665495807918080 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf113).numerator) (a-(83/256:ℝ)) /
      (50665495807918080:ℝ) = (1/360:ℝ)*evalZ (SourceBasis.rf113).numerator a
    simp only [SourceBasis.rf113]
    nlinarith [hh]
  · have hh := RFChecks.e113d.sound RFChecks.e113d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e113d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e113d.left 0)=factorCoefficients (BasisData.rf113).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e113d.target0=affineShift (SourceBasis.rf113).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf113).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(20266198323167232:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf113).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(20266198323167232:ℤ)] (a-(83/256:ℝ))=(20266198323167232:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf113] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf113).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf113).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/72:ℝ)*evalZ (SourceBasis.rf113).denominator a
    simp only [SourceBasis.rf113]
    nlinarith [hh]
  · norm_num [BasisData.rf113,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf114_translation (a : ℝ) :
    (BasisData.rf114).eval (a-83/256)=(SourceBasis.rf114).eval a := by
  apply translated_rf_of_scaled (BasisData.rf114) (SourceBasis.rf114) (1/360:ℝ) (1/72:ℝ) a (83/256)
  · have hh := RFChecks.e114n.sound RFChecks.e114n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e114n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e114n.left 0)=integerCoefficients (BasisData.rf114).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e114n.target0=affineShift (SourceBasis.rf114).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf114).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(25940733853654056960:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf114).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(12666373951979520:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(25940733853654056960:ℤ)] (a-(83/256:ℝ))=(25940733853654056960:ℝ) by simp [evalZ,horner]),(show evalZ [(12666373951979520:ℤ)] (a-(83/256:ℝ))=(12666373951979520:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf114] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf114).numerator.denominator = 12666373951979520 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf114).numerator) (a-(83/256:ℝ)) /
      (12666373951979520:ℝ) = (1/360:ℝ)*evalZ (SourceBasis.rf114).numerator a
    simp only [SourceBasis.rf114]
    nlinarith [hh]
  · have hh := RFChecks.e114d.sound RFChecks.e114d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e114d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e114d.left 0)=factorCoefficients (BasisData.rf114).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e114d.target0=affineShift (SourceBasis.rf114).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf114).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(20266198323167232:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf114).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(20266198323167232:ℤ)] (a-(83/256:ℝ))=(20266198323167232:ℝ) by simp [evalZ,horner]),(show evalZ [(1099511627776:ℤ)] (a-(83/256:ℝ))=(1099511627776:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf114] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf114).factors = 1099511627776 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf114).factors) (a-(83/256:ℝ)) /
      (1099511627776:ℝ) = (1/72:ℝ)*evalZ (SourceBasis.rf114).denominator a
    simp only [SourceBasis.rf114]
    nlinarith [hh]
  · norm_num [BasisData.rf114,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf115_translation (a : ℝ) :
    (BasisData.rf115).eval (a-83/256)=(SourceBasis.rf115).eval a := by
  apply translated_rf_of_scaled (BasisData.rf115) (SourceBasis.rf115) (1/9:ℝ) (1/9:ℝ) a (83/256)
  · have hh := RFChecks.e115n.sound RFChecks.e115n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e115n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e115n.left 0)=integerCoefficients (BasisData.rf115).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e115n.target0=affineShift (SourceBasis.rf115).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf115).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(150994944:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf115).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(294912:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(150994944:ℤ)] (a-(83/256:ℝ))=(150994944:ℝ) by simp [evalZ,horner]),(show evalZ [(294912:ℤ)] (a-(83/256:ℝ))=(294912:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf115] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf115).numerator.denominator = 294912 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf115).numerator) (a-(83/256:ℝ)) /
      (294912:ℝ) = (1/9:ℝ)*evalZ (SourceBasis.rf115).numerator a
    simp only [SourceBasis.rf115]
    nlinarith [hh]
  · have hh := RFChecks.e115d.sound RFChecks.e115d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e115d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e115d.left 0)=factorCoefficients (BasisData.rf115).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e115d.target0=affineShift (SourceBasis.rf115).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf115).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(589824:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf115).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(256:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(589824:ℤ)] (a-(83/256:ℝ))=(589824:ℝ) by simp [evalZ,horner]),(show evalZ [(256:ℤ)] (a-(83/256:ℝ))=(256:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf115] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf115).factors = 256 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf115).factors) (a-(83/256:ℝ)) /
      (256:ℝ) = (1/9:ℝ)*evalZ (SourceBasis.rf115).denominator a
    simp only [SourceBasis.rf115]
    nlinarith [hh]
  · norm_num [BasisData.rf115,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf116_translation (a : ℝ) :
    (BasisData.rf116).eval (a-83/256)=(SourceBasis.rf116).eval a := by
  apply translated_rf_of_scaled (BasisData.rf116) (SourceBasis.rf116) (1/20:ℝ) (1/4:ℝ) a (83/256)
  · have hh := RFChecks.e116n.sound RFChecks.e116n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e116n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e116n.left 0)=integerCoefficients (BasisData.rf116).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e116n.target0=affineShift (SourceBasis.rf116).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf116).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(21990232555520:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf116).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(85899345920:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(21990232555520:ℤ)] (a-(83/256:ℝ))=(21990232555520:ℝ) by simp [evalZ,horner]),(show evalZ [(85899345920:ℤ)] (a-(83/256:ℝ))=(85899345920:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf116] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf116).numerator.denominator = 85899345920 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf116).numerator) (a-(83/256:ℝ)) /
      (85899345920:ℝ) = (1/20:ℝ)*evalZ (SourceBasis.rf116).numerator a
    simp only [SourceBasis.rf116]
    nlinarith [hh]
  · have hh := RFChecks.e116d.sound RFChecks.e116d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e116d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e116d.left 0)=factorCoefficients (BasisData.rf116).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e116d.target0=affineShift (SourceBasis.rf116).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf116).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(4398046511104:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf116).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(4398046511104:ℤ)] (a-(83/256:ℝ))=(4398046511104:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf116] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf116).factors = 4294967296 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf116).factors) (a-(83/256:ℝ)) /
      (4294967296:ℝ) = (1/4:ℝ)*evalZ (SourceBasis.rf116).denominator a
    simp only [SourceBasis.rf116]
    nlinarith [hh]
  · norm_num [BasisData.rf116,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf117_translation (a : ℝ) :
    (BasisData.rf117).eval (a-83/256)=(SourceBasis.rf117).eval a := by
  apply translated_rf_of_scaled (BasisData.rf117) (SourceBasis.rf117) (1/20:ℝ) (1/4:ℝ) a (83/256)
  · have hh := RFChecks.e117n.sound RFChecks.e117n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e117n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e117n.left 0)=integerCoefficients (BasisData.rf117).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e117n.target0=affineShift (SourceBasis.rf117).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf117).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(5629499534213120:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf117).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(10995116277760:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(5629499534213120:ℤ)] (a-(83/256:ℝ))=(5629499534213120:ℝ) by simp [evalZ,horner]),(show evalZ [(10995116277760:ℤ)] (a-(83/256:ℝ))=(10995116277760:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf117] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf117).numerator.denominator = 10995116277760 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf117).numerator) (a-(83/256:ℝ)) /
      (10995116277760:ℝ) = (1/20:ℝ)*evalZ (SourceBasis.rf117).numerator a
    simp only [SourceBasis.rf117]
    nlinarith [hh]
  · have hh := RFChecks.e117d.sound RFChecks.e117d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e117d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e117d.left 0)=factorCoefficients (BasisData.rf117).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e117d.target0=affineShift (SourceBasis.rf117).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf117).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(4398046511104:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf117).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(4398046511104:ℤ)] (a-(83/256:ℝ))=(4398046511104:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf117] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf117).factors = 4294967296 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf117).factors) (a-(83/256:ℝ)) /
      (4294967296:ℝ) = (1/4:ℝ)*evalZ (SourceBasis.rf117).denominator a
    simp only [SourceBasis.rf117]
    nlinarith [hh]
  · norm_num [BasisData.rf117,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf118_translation (a : ℝ) :
    (BasisData.rf118).eval (a-83/256)=(SourceBasis.rf118).eval a := by
  apply translated_rf_of_scaled (BasisData.rf118) (SourceBasis.rf118) (1/20:ℝ) (1/4:ℝ) a (83/256)
  · have hh := RFChecks.e118n.sound RFChecks.e118n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e118n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e118n.left 0)=integerCoefficients (BasisData.rf118).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e118n.target0=affineShift (SourceBasis.rf118).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf118).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(5629499534213120:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf118).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(1374389534720:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(5629499534213120:ℤ)] (a-(83/256:ℝ))=(5629499534213120:ℝ) by simp [evalZ,horner]),(show evalZ [(1374389534720:ℤ)] (a-(83/256:ℝ))=(1374389534720:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf118] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf118).numerator.denominator = 1374389534720 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf118).numerator) (a-(83/256:ℝ)) /
      (1374389534720:ℝ) = (1/20:ℝ)*evalZ (SourceBasis.rf118).numerator a
    simp only [SourceBasis.rf118]
    nlinarith [hh]
  · have hh := RFChecks.e118d.sound RFChecks.e118d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e118d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e118d.left 0)=factorCoefficients (BasisData.rf118).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e118d.target0=affineShift (SourceBasis.rf118).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf118).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(4398046511104:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf118).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(4398046511104:ℤ)] (a-(83/256:ℝ))=(4398046511104:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf118] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf118).factors = 4294967296 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf118).factors) (a-(83/256:ℝ)) /
      (4294967296:ℝ) = (1/4:ℝ)*evalZ (SourceBasis.rf118).denominator a
    simp only [SourceBasis.rf118]
    nlinarith [hh]
  · norm_num [BasisData.rf118,ThomsonNegative.Compact.Packed.qval]
  · norm_num

theorem rf119_translation (a : ℝ) :
    (BasisData.rf119).eval (a-83/256)=(SourceBasis.rf119).eval a := by
  apply translated_rf_of_scaled (BasisData.rf119) (SourceBasis.rf119) (1/40:ℝ) (1/8:ℝ) a (83/256)
  · have hh := RFChecks.e119n.sound RFChecks.e119n_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e119n.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e119n.left 0)=integerCoefficients (BasisData.rf119).numerator := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e119n.target0=affineShift (SourceBasis.rf119).numerator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (integerCoefficients (BasisData.rf119).numerator) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(2882303761517117440:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf119).numerator 83 256) (a-(83/256:ℝ))*
      evalZ [(11258999068426240:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(2882303761517117440:ℤ)] (a-(83/256:ℝ))=(2882303761517117440:ℝ) by simp [evalZ,horner]),(show evalZ [(11258999068426240:ℤ)] (a-(83/256:ℝ))=(11258999068426240:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf119] at hh
    rw [polyData_eval]
    have hden : (BasisData.rf119).numerator.denominator = 11258999068426240 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (integerCoefficients (BasisData.rf119).numerator) (a-(83/256:ℝ)) /
      (11258999068426240:ℝ) = (1/40:ℝ)*evalZ (SourceBasis.rf119).numerator a
    simp only [SourceBasis.rf119]
    nlinarith [hh]
  · have hh := RFChecks.e119d.sound RFChecks.e119d_ok (a-(83/256:ℝ))
    simp only [show RFChecks.e119d.terms=1 from rfl,Finset.sum_range_one] at hh
    have hleft : ThomsonNegative.Structure.Exact.recCoeffs (RFChecks.e119d.left 0)=factorCoefficients (BasisData.rf119).factors := by decide +kernel
    have hshift : ThomsonNegative.Structure.Exact.recCoeffs RFChecks.e119d.target0=affineShift (SourceBasis.rf119).denominator 83 256 := by decide +kernel
    rw [hleft,hshift] at hh
    change (evalZ (factorCoefficients (BasisData.rf119).factors) (a-(83/256:ℝ))*
      evalZ [1] (a-(83/256:ℝ)))*evalZ [(8796093022208:ℤ)] (a-(83/256:ℝ)) =
      evalZ (affineShift (SourceBasis.rf119).denominator 83 256) (a-(83/256:ℝ))*
      evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))*evalZ [1] (a-(83/256:ℝ)) at hh
    simp only [(show evalZ [(1:ℤ)] (a-(83/256:ℝ))=(1:ℝ) by simp [evalZ,horner]),(show evalZ [(8796093022208:ℤ)] (a-(83/256:ℝ))=(8796093022208:ℝ) by simp [evalZ,horner]),(show evalZ [(4294967296:ℤ)] (a-(83/256:ℝ))=(4294967296:ℝ) by simp [evalZ,horner]),mul_one] at hh
    rw [affineShift_eval _ 83 256 (by norm_num)] at hh
    norm_num only [Int.cast_ofNat] at hh
    rw [show a-(83/256:ℝ)+(83:ℝ)/256=a by ring] at hh
    norm_num [SourceBasis.rf119] at hh
    rw [factorProduct_eval]
    have hden : factorDenominator (BasisData.rf119).factors = 4294967296 := by decide +kernel
    rw [hden]
    norm_num only [Nat.cast_ofNat]
    change evalZ (factorCoefficients (BasisData.rf119).factors) (a-(83/256:ℝ)) /
      (4294967296:ℝ) = (1/8:ℝ)*evalZ (SourceBasis.rf119).denominator a
    simp only [SourceBasis.rf119]
    nlinarith [hh]
  · norm_num [BasisData.rf119,ThomsonNegative.Compact.Packed.qval]
  · norm_num

#print axioms rf110_translation
end ThomsonNegative.Certificate.Bridges
