import AllS.Units.N_FI.N_image_equality.N_vanishing_features
import AllS.Units.N_F.N_energy_lower

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

theorem weightedOuterRep_eq_zero_of_strict_pairing {n : ℕ}
    (W M : Matrix (Fin n) (Fin n) ℝ) (hW : W.PosDef)
    (hM : WeightedOuterRep M) (hz : gramMatrixPairing W M=0) : M=0 := by
  obtain ⟨N,w,v,hw,hrep⟩ := hM
  have hsum : (∑ t,w t*dotProduct (v t) (W.mulVec (v t)))=0 := by
    rw [hrep,gramMatrixPairing_sum] at hz
    simpa only [gramMatrixPairing_smul,gramMatrixPairing_outer] using hz
  have hvan := image_equality_vanishing_features n N W hW w v hw hsum
  rw [hrep]
  apply Finset.sum_eq_zero
  intro t ht
  rcases hvan t with ht | ht
  · simp [ht]
  · ext i j
    simp [ht,Matrix.vecMulVec,Matrix.of_apply]

def ArbitraryGramsContract : Prop := ∀ s a D m,∀ h : Certificate s a D m,
  ∀ Y : Configuration,IsConfiguration Y → E s Y=E s (X a) →
  ∀ p : MomentPivots (D/2),∀ β : ℝ,∀ W : GramFamily (D/2),
  (∀ b,(W.val b).PosDef) → gramPoly a (D/2) p W=normalizedTarget s a β m →
  ∀ V : GramFamily (D/2),distinctPolySum Y (gramPoly a (D/2) p V)=0

theorem equality_block_moment_zero {s a : ℝ} {D : ℕ} {m : Fin 5 → ℕ}
    (h : Certificate s a D m) (Y : Configuration) (hY : IsConfiguration Y)
    (he : E s Y=E s (X a)) (p : MomentPivots (D/2)) (β : ℝ) (W : GramFamily (D/2))
    (hW : ∀ b,(W.val b).PosDef) (hpoly : gramPoly a (D/2) p W=normalizedTarget s a β m)
    (b : GramBlock (D/2)) : gramBlockMoment Y a (D/2) p b=0 :=
  weightedOuterRep_eq_zero_of_strict_pairing _ _ (hW b)
    (moment_pos_weighted_outer_products Y hY.1 a (D/2) p b)
    (equality_block_pairing_zero h Y hY he p β W hW hpoly b)

theorem image_equality_arbitrary_grams : ArbitraryGramsContract := by
  intro s a D m h Y hY he p β W hW hpoly V
  rw [distinct_gramPoly_pairing]
  apply Finset.sum_eq_zero
  intro b hb
  rw [equality_block_moment_zero h Y hY he p β W hW hpoly b]
  simp [gramMatrixPairing]

#check image_equality_arbitrary_grams
#print axioms image_equality_arbitrary_grams
end Blueprint.Thomson.Finite
