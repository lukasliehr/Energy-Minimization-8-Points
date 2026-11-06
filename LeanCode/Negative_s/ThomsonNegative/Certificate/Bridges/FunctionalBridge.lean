import ThomsonNegative.Certificate.Bridges.FunctionalRows00
import ThomsonNegative.Certificate.Bridges.FunctionalRows01
import ThomsonNegative.Certificate.Bridges.FunctionalRows02
import ThomsonNegative.Certificate.Bridges.FunctionalRows03
import ThomsonNegative.Certificate.Bridges.FunctionalRows04
import ThomsonNegative.Certificate.Bridges.FunctionalRows05
import ThomsonNegative.Certificate.Bridges.FunctionalRows06
import ThomsonNegative.Certificate.Bridges.FunctionalRows07
import ThomsonNegative.Certificate.Bridges.FunctionalRows08
import ThomsonNegative.Certificate.Bridges.FunctionalRows09
import ThomsonNegative.Certificate.Bridges.FunctionalRows10
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem functionalRows_polynomial (i : Fin 102) :
    familyPolynomial (invariantMonomial (fullTag i))=functionalPolynomial i := by
  fin_cases i
  · exact functionalRow000_polynomial
  · exact functionalRow001_polynomial
  · exact functionalRow002_polynomial
  · exact functionalRow003_polynomial
  · exact functionalRow004_polynomial
  · exact functionalRow005_polynomial
  · exact functionalRow006_polynomial
  · exact functionalRow007_polynomial
  · exact functionalRow008_polynomial
  · exact functionalRow009_polynomial
  · exact functionalRow010_polynomial
  · exact functionalRow011_polynomial
  · exact functionalRow012_polynomial
  · exact functionalRow013_polynomial
  · exact functionalRow014_polynomial
  · exact functionalRow015_polynomial
  · exact functionalRow016_polynomial
  · exact functionalRow017_polynomial
  · exact functionalRow018_polynomial
  · exact functionalRow019_polynomial
  · exact functionalRow020_polynomial
  · exact functionalRow021_polynomial
  · exact functionalRow022_polynomial
  · exact functionalRow023_polynomial
  · exact functionalRow024_polynomial
  · exact functionalRow025_polynomial
  · exact functionalRow026_polynomial
  · exact functionalRow027_polynomial
  · exact functionalRow028_polynomial
  · exact functionalRow029_polynomial
  · exact functionalRow030_polynomial
  · exact functionalRow031_polynomial
  · exact functionalRow032_polynomial
  · exact functionalRow033_polynomial
  · exact functionalRow034_polynomial
  · exact functionalRow035_polynomial
  · exact functionalRow036_polynomial
  · exact functionalRow037_polynomial
  · exact functionalRow038_polynomial
  · exact functionalRow039_polynomial
  · exact functionalRow040_polynomial
  · exact functionalRow041_polynomial
  · exact functionalRow042_polynomial
  · exact functionalRow043_polynomial
  · exact functionalRow044_polynomial
  · exact functionalRow045_polynomial
  · exact functionalRow046_polynomial
  · exact functionalRow047_polynomial
  · exact functionalRow048_polynomial
  · exact functionalRow049_polynomial
  · exact functionalRow050_polynomial
  · exact functionalRow051_polynomial
  · exact functionalRow052_polynomial
  · exact functionalRow053_polynomial
  · exact functionalRow054_polynomial
  · exact functionalRow055_polynomial
  · exact functionalRow056_polynomial
  · exact functionalRow057_polynomial
  · exact functionalRow058_polynomial
  · exact functionalRow059_polynomial
  · exact functionalRow060_polynomial
  · exact functionalRow061_polynomial
  · exact functionalRow062_polynomial
  · exact functionalRow063_polynomial
  · exact functionalRow064_polynomial
  · exact functionalRow065_polynomial
  · exact functionalRow066_polynomial
  · exact functionalRow067_polynomial
  · exact functionalRow068_polynomial
  · exact functionalRow069_polynomial
  · exact functionalRow070_polynomial
  · exact functionalRow071_polynomial
  · exact functionalRow072_polynomial
  · exact functionalRow073_polynomial
  · exact functionalRow074_polynomial
  · exact functionalRow075_polynomial
  · exact functionalRow076_polynomial
  · exact functionalRow077_polynomial
  · exact functionalRow078_polynomial
  · exact functionalRow079_polynomial
  · exact functionalRow080_polynomial
  · exact functionalRow081_polynomial
  · exact functionalRow082_polynomial
  · exact functionalRow083_polynomial
  · exact functionalRow084_polynomial
  · exact functionalRow085_polynomial
  · exact functionalRow086_polynomial
  · exact functionalRow087_polynomial
  · exact functionalRow088_polynomial
  · exact functionalRow089_polynomial
  · exact functionalRow090_polynomial
  · exact functionalRow091_polynomial
  · exact functionalRow092_polynomial
  · exact functionalRow093_polynomial
  · exact functionalRow094_polynomial
  · exact functionalRow095_polynomial
  · exact functionalRow096_polynomial
  · exact functionalRow097_polynomial
  · exact functionalRow098_polynomial
  · exact functionalRow099_polynomial
  · exact functionalRow100_polynomial
  · exact functionalRow101_polynomial
theorem functionalRows_derivative (i : Fin 102) :
    (functionalPolynomial i).derivative=functionalSlopePolynomial i := by
  fin_cases i
  · exact functionalRow000_derivative
  · exact functionalRow001_derivative
  · exact functionalRow002_derivative
  · exact functionalRow003_derivative
  · exact functionalRow004_derivative
  · exact functionalRow005_derivative
  · exact functionalRow006_derivative
  · exact functionalRow007_derivative
  · exact functionalRow008_derivative
  · exact functionalRow009_derivative
  · exact functionalRow010_derivative
  · exact functionalRow011_derivative
  · exact functionalRow012_derivative
  · exact functionalRow013_derivative
  · exact functionalRow014_derivative
  · exact functionalRow015_derivative
  · exact functionalRow016_derivative
  · exact functionalRow017_derivative
  · exact functionalRow018_derivative
  · exact functionalRow019_derivative
  · exact functionalRow020_derivative
  · exact functionalRow021_derivative
  · exact functionalRow022_derivative
  · exact functionalRow023_derivative
  · exact functionalRow024_derivative
  · exact functionalRow025_derivative
  · exact functionalRow026_derivative
  · exact functionalRow027_derivative
  · exact functionalRow028_derivative
  · exact functionalRow029_derivative
  · exact functionalRow030_derivative
  · exact functionalRow031_derivative
  · exact functionalRow032_derivative
  · exact functionalRow033_derivative
  · exact functionalRow034_derivative
  · exact functionalRow035_derivative
  · exact functionalRow036_derivative
  · exact functionalRow037_derivative
  · exact functionalRow038_derivative
  · exact functionalRow039_derivative
  · exact functionalRow040_derivative
  · exact functionalRow041_derivative
  · exact functionalRow042_derivative
  · exact functionalRow043_derivative
  · exact functionalRow044_derivative
  · exact functionalRow045_derivative
  · exact functionalRow046_derivative
  · exact functionalRow047_derivative
  · exact functionalRow048_derivative
  · exact functionalRow049_derivative
  · exact functionalRow050_derivative
  · exact functionalRow051_derivative
  · exact functionalRow052_derivative
  · exact functionalRow053_derivative
  · exact functionalRow054_derivative
  · exact functionalRow055_derivative
  · exact functionalRow056_derivative
  · exact functionalRow057_derivative
  · exact functionalRow058_derivative
  · exact functionalRow059_derivative
  · exact functionalRow060_derivative
  · exact functionalRow061_derivative
  · exact functionalRow062_derivative
  · exact functionalRow063_derivative
  · exact functionalRow064_derivative
  · exact functionalRow065_derivative
  · exact functionalRow066_derivative
  · exact functionalRow067_derivative
  · exact functionalRow068_derivative
  · exact functionalRow069_derivative
  · exact functionalRow070_derivative
  · exact functionalRow071_derivative
  · exact functionalRow072_derivative
  · exact functionalRow073_derivative
  · exact functionalRow074_derivative
  · exact functionalRow075_derivative
  · exact functionalRow076_derivative
  · exact functionalRow077_derivative
  · exact functionalRow078_derivative
  · exact functionalRow079_derivative
  · exact functionalRow080_derivative
  · exact functionalRow081_derivative
  · exact functionalRow082_derivative
  · exact functionalRow083_derivative
  · exact functionalRow084_derivative
  · exact functionalRow085_derivative
  · exact functionalRow086_derivative
  · exact functionalRow087_derivative
  · exact functionalRow088_derivative
  · exact functionalRow089_derivative
  · exact functionalRow090_derivative
  · exact functionalRow091_derivative
  · exact functionalRow092_derivative
  · exact functionalRow093_derivative
  · exact functionalRow094_derivative
  · exact functionalRow095_derivative
  · exact functionalRow096_derivative
  · exact functionalRow097_derivative
  · exact functionalRow098_derivative
  · exact functionalRow099_derivative
  · exact functionalRow100_derivative
  · exact functionalRow101_derivative
lemma physicalSynthesize_sum (v : FullSpace) :
    physicalSynthesize v=∑ i : Fin 102,v i • invariantMonomial (fullTag i) := by
  change invariantSubst (∑ i : Fin 102,MvPolynomial.C (v i)*coordinateMonomial (fullTag i))=_
  simp only [map_sum,map_mul,invariantSubst_coordinateMonomial,MvPolynomial.smul_eq_C_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simp [invariantSubst]

theorem familyPolynomial_fullCoordinates (v : FullSpace) :
    familyPolynomial (physicalSynthesize v)=∑ i : Fin 102,v i • functionalPolynomial i := by
  rw [physicalSynthesize_sum,map_sum]
  simp only [map_smul,functionalRows_polynomial]

theorem coefficientEll0_rows (a : ℝ) (v : FullSpace) :
    coefficientEll0 a v=∑ i : Fin 102,v i*
      (Packed.evalZ (Exact.recCoeffs (Factored.FunctionalData.numerator i.val)) a /
        Factored.FunctionalData.denominator i.val) := by
  change Polynomial.eval a (familyPolynomial (physicalSynthesize v))=_
  rw [familyPolynomial_fullCoordinates]
  simp only [Polynomial.eval_finsetSum,Polynomial.eval_smul,functionalPolynomial,
    Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem coefficientEll1_rows (a : ℝ) (v : FullSpace) :
    coefficientEll1 a v=∑ i : Fin 102,v i*
      (Packed.evalZ (Exact.recCoeffs (Factored.FunctionalData.slopeNumerator i.val)) a /
        Factored.FunctionalData.denominator i.val) := by
  change Polynomial.eval a (familyPolynomial (physicalSynthesize v)).derivative=_
  rw [familyPolynomial_fullCoordinates]
  simp only [Polynomial.derivative_sum,Polynomial.derivative_smul,functionalRows_derivative,
    Polynomial.eval_finsetSum,Polynomial.eval_smul,functionalSlopePolynomial,
    Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

#print axioms coefficientEll0_rows
#print axioms coefficientEll1_rows
end ThomsonNegative.Certificate.Bridges
