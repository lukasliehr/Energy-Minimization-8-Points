import AllS.Units.N_AI.N_fixed_tables.GramCombinationSupport

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

/-- A source polynomial for every entry of every actual Gram block. Empty
blocks contribute zero by the ordinary finite sum convention. -/
def fixedGramSource {d : ℕ}
    (K : (b : GramBlock d) → Fin (gramBlockDimension d b) →
      Fin (gramBlockDimension d b) → Poly3) (W : GramFamily d) : Poly3 :=
  ∑ b,∑ i,∑ j,MvPolynomial.C (W.val b i j)*K b i j

theorem fixedGramSource_canonical {d : ℕ} (a : ℝ) (p : MomentPivots d)
    (K : (b : GramBlock d) → Fin (gramBlockDimension d b) →
      Fin (gramBlockDimension d b) → Poly3)
    (hK : ∀ b i j,invariantSubst (K b i j)=gramKernel a d p b i j)
    (W : GramFamily d) : invariantSubst (fixedGramSource K W)=gramPoly a d p W := by
  simp only [fixedGramSource,map_sum,map_mul,hK,gramPoly]
  simp [invariantSubst]

theorem fixedGramSource_coefficient {d : ℕ}
    (K : (b : GramBlock d) → Fin (gramBlockDimension d b) →
      Fin (gramBlockDimension d b) → Poly3) (W : GramFamily d) (t : Tag) :
    MvPolynomial.coeff (tagExponent t) (fixedGramSource K W)=
      ∑ b,∑ i,∑ j,W.val b i j*MvPolynomial.coeff (tagExponent t) (K b i j) := by
  simp only [fixedGramSource,MvPolynomial.coeff_sum,MvPolynomial.coeff_C_mul]

#print axioms fixedGramSource_canonical
#print axioms fixedGramSource_coefficient
end Blueprint.Thomson.Finite
