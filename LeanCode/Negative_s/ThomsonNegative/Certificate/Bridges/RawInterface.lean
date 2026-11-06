import ThomsonNegative.Certificate.Bridges.Basis
import ThomsonNegative.Certificate.Bridges.RawMix
import ThomsonNegative.Certificate.Bridges.RawSynthesis

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure

def rawSize : Block → Nat := ![7,6,5,4,3,2,16,18]

def blockBasis (B : CanonicalBasis) : (b : Block) →
    Matrix (Fin (rawSize b)) (Fin (blockSize b)) ℝ :=
  Fin.cases (B.moment 0)
    (Fin.cases (B.moment 1)
      (Fin.cases (B.moment 2)
        (Fin.cases (B.moment 3)
          (Fin.cases (B.moment 4)
            (Fin.cases (B.moment 5)
              (Fin.cases B.plus (Fin.cases B.standard (fun i => Fin.elim0 i))))))))

def rawPhysical : (b : Block) → Matrix (Fin (rawSize b)) (Fin (rawSize b)) Poly3 :=
  Fin.cases (fun i j => kernelRPolynomial 0 i.val j.val)
    (Fin.cases (fun i j => kernelRPolynomial 1 i.val j.val)
      (Fin.cases (fun i j => kernelRPolynomial 2 i.val j.val)
        (Fin.cases (fun i j => kernelRPolynomial 3 i.val j.val)
          (Fin.cases (fun i j => kernelRPolynomial 4 i.val j.val)
            (Fin.cases (fun i j => kernelRPolynomial 5 i.val j.val)
              (Fin.cases rawPlusPolynomial (Fin.cases rawStandardPolynomial (fun i => Fin.elim0 i))))))))

def rawCoefficient (b : Block) (ℓ : Fin 102) (r s : Fin (rawSize b)) : ℝ :=
  (RawData.coefficient b.val ℓ.val r.val s.val:ℝ)/RawData.denominator b.val

theorem blockBasis_source_entry (a : ℝ) (b : Block) (r : Fin (rawSize b)) (i : Fin (blockSize b)) :
    blockBasis (sourceBasis.eval a) b r i=
      (SourceBasis.record (BasisLayout.index b.val r.val i.val)).eval a := by
  fin_cases b <;> rfl

theorem blockBasis_encoded_entry (a : ℝ) (b : Block) (r : Fin (rawSize b)) (i : Fin (blockSize b)) :
    blockBasis (sourceBasis.eval a) b r i=
      (BasisData.record (BasisLayout.index b.val r.val i.val)).eval (a-83/256) := by
  rw [← encodedBasis_eq_source]
  fin_cases b <;> rfl

def rawCoefficientVector (b : Block) (r s : Fin (rawSize b)) : FullSpace :=
  fun ℓ => rawCoefficient b ℓ r s

def mixedCoefficient (B : CanonicalBasis) (b : Block) (i j : Fin (blockSize b)) : FullSpace :=
  ∑ r, ∑ s, (blockBasis B b r i*blockBasis B b s j) • rawCoefficientVector b r s

def coefficientMap (a : ℝ) : GramFamily →ₗ[ℝ] FullSpace where
  toFun W := ∑ b, ∑ i, ∑ j, W b i j • mixedCoefficient (sourceBasis.eval a) b i j
  map_add' W V := by
    simp only [Pi.add_apply,Matrix.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' c W := by
    simp only [Pi.smul_apply,Matrix.smul_apply,smul_eq_mul,RingHom.id_apply,
      mul_smul,Finset.smul_sum]

theorem coefficientMap_apply (a : ℝ) (W : GramFamily) (ℓ : Fin 102) :
    coefficientMap a W ℓ=∑ b,∑ i,∑ j,W b i j*
      ∑ r,∑ s,blockBasis (sourceBasis.eval a) b r i*blockBasis (sourceBasis.eval a) b s j*
        rawCoefficient b ℓ r s := by
  simp [coefficientMap,mixedCoefficient,rawCoefficientVector]

lemma canonicalPolynomialFamily_mix (B : CanonicalBasis) (b : Block)
    (i j : Fin (blockSize b)) :
    canonicalPolynomialFamily B b i j=quadraticMix (blockBasis B b) (rawPhysical b) i j := by
  fin_cases b
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact plusPolynomial_mix B.plus i j
  · exact standardPolynomial_mix B.standard i j

end ThomsonNegative.Certificate.Bridges
