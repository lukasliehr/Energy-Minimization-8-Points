import AllS.Units.N_AI.N_fixed_tables.GramInsertionSupport
import AllS.Units.N_AI.N_fixed_tables.ProjectionCoefficientSupport

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

/-- The proved Gram polynomial map, as an actual linear map. -/
def fixedGramPolyLinear (a : ℝ) (d : ℕ) (p : MomentPivots d) :
    GramFamily d →ₗ[ℝ] Poly3 where
  toFun := gramPoly a d p
  map_add' := gramPoly_add a d p
  map_smul' := by intro c W;exact gramPoly_smul a d p W c

theorem gramPoly_sum {n : ℕ} (a : ℝ) (d : ℕ) (p : MomentPivots d)
    (W : Fin n → GramFamily d) :
    gramPoly a d p (∑ j,W j)=∑ j,gramPoly a d p (W j) :=
  map_sum (fixedGramPolyLinear a d p) W Finset.univ

def fixedSourceCombination {n : ℕ} (P : Fin n → Poly3) (v : Fin n → ℝ) : Poly3 :=
  ∑ j,MvPolynomial.C (v j)*P j

theorem fixedSourceCombination_canonical {n d : ℕ} (a : ℝ) (p : MomentPivots d)
    (P : Fin n → Poly3) (U : Fin n → GramFamily d)
    (h : ∀ j,invariantSubst (P j)=gramPoly a d p (U j)) (v : Fin n → ℝ) :
    invariantSubst (fixedSourceCombination P v)=gramPoly a d p (∑ j,v j • U j) := by
  rw [fixedSourceCombination,map_sum,gramPoly_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_mul,h j,gramPoly_smul]
  simp [invariantSubst,MvPolynomial.smul_eq_C_mul]

theorem fixedSourceCombination_coefficient {n m : ℕ} (tags : Fin m → Tag)
    (P : Fin n → Poly3) (v : Fin n → ℝ) (i : Fin m) :
    MvPolynomial.coeff (tagExponent (tags i)) (fixedSourceCombination P v)=
      (Matrix.of (fun i j => MvPolynomial.coeff (tagExponent (tags i)) (P j))).mulVec v i := by
  simp only [fixedSourceCombination,MvPolynomial.coeff_sum,MvPolynomial.coeff_C_mul,
    Matrix.mulVec,Matrix.of_apply,dotProduct]
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

#print axioms fixedSourceCombination_canonical
#print axioms fixedSourceCombination_coefficient
end Blueprint.Thomson.Finite
