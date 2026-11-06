import ThomsonNegative.Certificate.Bridges.RawInterface
import ThomsonNegative.Certificate.Bridges.RawCatalogue

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem rawCoefficientVector_physical (b : Block) (r s : Fin (rawSize b)) :
    physicalSynthesize (rawCoefficientVector b r s)=rawPhysical b r s := by
  change invariantSubst (rawCoordinate b.val r.val s.val)=rawPhysical b r s
  fin_cases b
  · exact rawBlock0_physical r s
  · exact rawBlock1_physical r s
  · exact rawBlock2_physical r s
  · exact rawBlock3_physical r s
  · exact rawBlock4_physical r s
  · exact rawBlock5_physical r s
  · exact rawBlock6_physical r s
  · exact rawBlock7_physical r s

theorem mixedCoefficient_physical (B : CanonicalBasis) (b : Block) (i j : Fin (blockSize b)) :
    physicalSynthesize (mixedCoefficient B b i j)=canonicalPolynomialFamily B b i j := by
  simp only [mixedCoefficient,map_sum,map_smul,rawCoefficientVector_physical]
  rw [canonicalPolynomialFamily_mix]
  simp only [quadraticMix,MvPolynomial.smul_eq_C_mul]

theorem coefficientMap_physical (a : ℝ) (W : GramFamily) :
    physicalSynthesize (coefficientMap a W)=gramPolynomial (sourcePolynomialFamily a) W := by
  change physicalSynthesize (∑ b, ∑ i, ∑ j, W b i j • mixedCoefficient (sourceBasis.eval a) b i j)=_
  simp only [map_sum,map_smul,mixedCoefficient_physical,MvPolynomial.smul_eq_C_mul]
  rfl

#print axioms rawCoefficientVector_physical
#print axioms coefficientMap_physical
end ThomsonNegative.Certificate.Bridges
