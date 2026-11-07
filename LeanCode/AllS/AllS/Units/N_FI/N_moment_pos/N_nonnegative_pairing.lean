import AllS.Units.N_FI.N_moment_pos.N_weighted_outer_products

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

def gramMatrixPairing {n : ℕ} (W M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i,∑ j,W i j*M i j

def GramPairingNonnegativeContract : Prop := ∀ a d p,∀ W : GramFamily d,
  (∀ b,(W.val b).PosSemidef) → ∀ Y : Configuration,(∀ i,‖Y i‖=1) →
    0 ≤ distinctPolySum Y (gramPoly a d p W)

theorem gramMatrixPairing_sum {n : ℕ} {ι : Type*}
    (W : Matrix (Fin n) (Fin n) ℝ) (s : Finset ι) (f : ι → Matrix (Fin n) (Fin n) ℝ) :
    gramMatrixPairing W (∑ t∈s,f t)=∑ t∈s,gramMatrixPairing W (f t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [gramMatrixPairing]
  | @insert t s ht h =>
    simp only [Finset.sum_insert ht]
    rw [show gramMatrixPairing W (f t+∑ x∈s,f x)=
        gramMatrixPairing W (f t)+gramMatrixPairing W (∑ x∈s,f x) by
      simp [gramMatrixPairing,mul_add,Finset.sum_add_distrib]]
    rw [h]

theorem gramMatrixPairing_smul {n : ℕ} (W M : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    gramMatrixPairing W (c • M)=c*gramMatrixPairing W M := by
  simp only [gramMatrixPairing,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem gramMatrixPairing_outer {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    gramMatrixPairing W (Matrix.vecMulVec v v)=dotProduct v (W.mulVec v) := by
  simp only [gramMatrixPairing,Matrix.vecMulVec,Matrix.of_apply,Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem gramMatrixPairing_nonneg {n : ℕ} (W M : Matrix (Fin n) (Fin n) ℝ)
    (hW : W.PosSemidef) (hM : WeightedOuterRep M) : 0 ≤ gramMatrixPairing W M := by
  obtain ⟨N,w,v,hw,rfl⟩ := hM
  rw [gramMatrixPairing_sum]
  apply Finset.sum_nonneg
  intro t ht
  rw [gramMatrixPairing_smul,gramMatrixPairing_outer]
  exact mul_nonneg (hw t) (by simpa only [star_trivial] using hW.dotProduct_mulVec_nonneg (v t))

theorem distinct_gramPoly_pairing (Y : Configuration) (a : ℝ) (d : ℕ)
    (p : MomentPivots d) (W : GramFamily d) :
    distinctPolySum Y (gramPoly a d p W)=
      ∑ b : GramBlock d,gramMatrixPairing (W.val b) (gramBlockMoment Y a d p b) := by
  simp only [gramPoly,distinctPolySum_sum,distinctPolySum_C_mul,gramMatrixPairing,gramBlockMoment]

theorem moment_pos_nonnegative_pairing : GramPairingNonnegativeContract := by
  intro a d p W hW Y hY
  rw [distinct_gramPoly_pairing]
  apply Finset.sum_nonneg
  intro b hb
  exact gramMatrixPairing_nonneg _ _ (hW b) (moment_pos_weighted_outer_products Y hY a d p b)

#check moment_pos_nonnegative_pairing
#print axioms moment_pos_nonnegative_pairing
end Blueprint.Thomson.Finite
