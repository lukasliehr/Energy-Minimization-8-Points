import ThomsonNegative.Structure.Concrete.NullSound

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure ThomsonNegative.Structure.Concrete

def functionalRawMatrix (L : FullSpace →ₗ[ℝ] ℝ) (b : Block) :
    Matrix (Fin (rawSize b)) (Fin (rawSize b)) ℝ := fun r s => L (rawCoefficientVector b r s)

lemma mixedCoefficient_functional (L : FullSpace →ₗ[ℝ] ℝ) (B : CanonicalBasis)
    (b : Block) (i j : Fin (blockSize b)) :
    L (mixedCoefficient B b i j)=
      ((blockBasis B b).transpose*functionalRawMatrix L b*blockBasis B b) i j := by
  simp only [mixedCoefficient,map_sum,map_smul,smul_eq_mul,Matrix.mul_apply,
    Matrix.transpose_apply,Finset.sum_mul,functionalRawMatrix]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro r hr
  ring

lemma sourceBasis_cleared (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) (b : Block) :
    blockBasis (sourceBasis.eval a) b=(basisDenominator a b)⁻¹ • clearedBasis a b := by
  ext r i
  rw [clearedBasis_source a ha hb]
  simp only [Matrix.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]

lemma sourceValue_sandwich (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) (b : Block) :
    (blockBasis (sourceBasis.eval a) b).transpose*rawValueMatrix a b*
      blockBasis (sourceBasis.eval a) b=0 := by
  rw [sourceBasis_cleared a ha hb]
  simp only [Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  rw [Matrix.mul_assoc,rawValueMatrix_null,Matrix.mul_zero,smul_zero]

lemma sourceSlope_sandwich (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) (b : Block) :
    (blockBasis (sourceBasis.eval a) b).transpose*rawSlopeMatrix a b*
      blockBasis (sourceBasis.eval a) b=0 := by
  rw [sourceBasis_cleared a ha hb]
  simp only [Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  rw [rawSlopeMatrix_sandwich,smul_zero]

lemma mixedCoefficient_ell0_image (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3)
    (b : Block) (i j : Fin (blockSize b)) :
    coefficientEll0 a (mixedCoefficient (sourceBasis.eval a) b i j)=0 := by
  rw [mixedCoefficient_functional]
  change ((blockBasis (sourceBasis.eval a) b).transpose*rawValueMatrix a b*
    blockBasis (sourceBasis.eval a) b) i j=0
  rw [sourceValue_sandwich a ha hb]
  rfl

lemma mixedCoefficient_ell1_image (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3)
    (b : Block) (i j : Fin (blockSize b)) :
    coefficientEll1 a (mixedCoefficient (sourceBasis.eval a) b i j)=0 := by
  rw [mixedCoefficient_functional]
  change ((blockBasis (sourceBasis.eval a) b).transpose*rawSlopeMatrix a b*
    blockBasis (sourceBasis.eval a) b) i j=0
  rw [sourceSlope_sandwich a ha hb]
  rfl

theorem coefficientMap_ell0_image (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) (W : GramFamily) :
    coefficientEll0 a (coefficientMap a W)=0 := by
  simp only [coefficientMap,LinearMap.coe_mk,AddHom.coe_mk,map_sum,map_smul,
    mixedCoefficient_ell0_image a ha hb,smul_zero,Finset.sum_const_zero]

theorem coefficientMap_ell1_image (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) (W : GramFamily) :
    coefficientEll1 a (coefficientMap a W)=0 := by
  simp only [coefficientMap,LinearMap.coe_mk,AddHom.coe_mk,map_sum,map_smul,
    mixedCoefficient_ell1_image a ha hb,smul_zero,Finset.sum_const_zero]

#print axioms coefficientMap_ell0_image
#print axioms coefficientMap_ell1_image
end ThomsonNegative.Certificate.Bridges
