import AllS.Units.N_FI.N_gram_map.N_physical_entries

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite
set_option maxHeartbeats 0

/-- One physical upper-triangle coordinate: a diagonal is inserted once and an
    off-diagonal is inserted in both symmetric positions. -/
def fixedSymmetricUnit {n : ℕ} (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  (if i=j then (1/2:ℝ) else 1) • physicalSymmetricEntry i j

theorem fixedSymmetricUnit_isSymm {n : ℕ} (i j : Fin n) :
    (fixedSymmetricUnit i j).IsSymm :=
  (physicalSymmetricEntry_isSymm i j).smul _

theorem gramBlockPoly_fixedSymmetricUnit (a : ℝ) (d : ℕ) (p : MomentPivots d)
    (b : GramBlock d) (i j : Fin (gramBlockDimension d b)) :
    gramBlockPoly a d p b (fixedSymmetricUnit i j)=
      MvPolynomial.C (if i=j then (1:ℝ) else 2)*gramKernel a d p b i j := by
  have hs (c : ℝ) (W : Matrix (Fin (gramBlockDimension d b)) (Fin (gramBlockDimension d b)) ℝ) :
      gramBlockPoly a d p b (c • W)=MvPolynomial.C c*gramBlockPoly a d p b W := by
    simp [gramBlockPoly,smul_eq_mul,Finset.mul_sum,mul_assoc]
  rw [fixedSymmetricUnit,hs,gramBlockPoly_physical_entry]
  by_cases hij : i=j
  · simp only [if_pos hij]
    rw [← mul_assoc,← map_mul]
    norm_num
  · simp [hij]

/-- Put one symmetric matrix into one actual mathematical Gram block. -/
def fixedSingleGram {d : ℕ} (b : GramBlock d)
    (W : Matrix (Fin (gramBlockDimension d b)) (Fin (gramBlockDimension d b)) ℝ)
    (hW : W.IsSymm) : GramFamily d := by
  classical
  refine ⟨Pi.single b W,?_⟩
  intro c
  by_cases h : c=b
  · subst c
    simpa using hW
  · simpa [Pi.single_eq_of_ne h] using (Matrix.isSymm_zero : (0 : Matrix (Fin (gramBlockDimension d c)) (Fin (gramBlockDimension d c)) ℝ).IsSymm)

theorem gramPoly_fixedSingleGram (a : ℝ) (d : ℕ) (p : MomentPivots d)
    (b : GramBlock d) (W : Matrix (Fin (gramBlockDimension d b)) (Fin (gramBlockDimension d b)) ℝ)
    (hW : W.IsSymm) :
    gramPoly a d p (fixedSingleGram b W hW)=gramBlockPoly a d p b W := by
  classical
  unfold gramPoly
  rw [Finset.sum_eq_single b]
  · simp [fixedSingleGram,gramBlockPoly]
  · intro c hc hcb
    simp [fixedSingleGram,Pi.single_eq_of_ne hcb]
  · simp

def fixedGramUnit {d : ℕ} (b : GramBlock d)
    (i j : Fin (gramBlockDimension d b)) : GramFamily d :=
  fixedSingleGram b (fixedSymmetricUnit i j) (fixedSymmetricUnit_isSymm i j)

theorem gramPoly_fixedGramUnit (a : ℝ) (d : ℕ) (p : MomentPivots d)
    (b : GramBlock d) (i j : Fin (gramBlockDimension d b)) :
    gramPoly a d p (fixedGramUnit b i j)=
      MvPolynomial.C (if i=j then (1:ℝ) else 2)*gramKernel a d p b i j := by
  rw [fixedGramUnit,gramPoly_fixedSingleGram,gramBlockPoly_fixedSymmetricUnit]

#print axioms gramPoly_fixedGramUnit
end Blueprint.Thomson.Finite
