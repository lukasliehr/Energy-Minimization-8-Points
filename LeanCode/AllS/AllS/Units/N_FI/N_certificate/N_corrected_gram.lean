import AllS.Units.N_FI.N_certificate.N_typed_contract
import AllS.Units.N_FI.N_compatibility.N_normalized_target
import AllS.Units.N_F.N_compatibility

noncomputable section
namespace Blueprint.Thomson.Finite

/-- The actual Gram polynomial, with its degree and compatibility equations. -/
def gramCompatible (a : ℝ) (ha : physical a) (D : ℕ) (hD : ActiveDegree D)
    (p : MomentPivots (D/2)) (hp : ValidMomentPivots p) :
    GramFamily (D/2) →ₗ[ℝ] Compatible a D where
  toFun W := ⟨gramPoly a (D/2) p W, by
    have hh := activeDegree_half hD
    simpa only [hh.2.2] using gramPoly_compatible a ha (D/2) hh.1 hh.2.1 p hp W⟩
  map_add' V W := Subtype.ext (gramPoly_add a (D/2) p V W)
  map_smul' c W := Subtype.ext (gramPoly_smul a (D/2) p W c)

/-- An exact correction is applied to the full compatible polynomial residual. -/
def correctedGram {a : ℝ} {D : ℕ}
    (A : GramFamily (D/2) →ₗ[ℝ] Compatible a D)
    (R : Compatible a D → GramFamily (D/2))
    (target : Compatible a D) (W0 : GramFamily (D/2)) : GramFamily (D/2) :=
  W0 + R (target - A W0)

theorem correctedGram_identity (a : ℝ) (ha : physical a) (D : ℕ) (hD : ActiveDegree D)
    (p : MomentPivots (D/2)) (hp : ValidMomentPivots p)
    (R : Compatible a D → GramFamily (D/2))
    (hR : ∀ f, gramPoly a (D/2) p (R f) = f.val)
    (target : Compatible a D) (W0 : GramFamily (D/2)) :
    gramPoly a (D/2) p (correctedGram (gramCompatible a ha D hD p hp) R target W0) =
      target.val := by
  rw [correctedGram,gramPoly_add,hR]
  change gramPoly a (D/2) p W0 + (target.val - gramPoly a (D/2) p W0) = target.val
  abel

def normalizedTargetCompatible (s a β : ℝ) (D : ℕ) (m : Fin 5 → ℕ)
    (hs : 0 ≤ s) (ha : physical a) (hroot : F s a = 0) (hm : Profile.Valid D m) :
    Compatible a D :=
  ⟨normalizedTarget s a β m,normalizedTarget_compatible s a β D m hs ha hroot hm⟩

/-- A right inverse and positive corrected physical blocks produce the complete
mathematical certificate; no arithmetic receipt is an assumption. -/
theorem certificate_of_exact_gram_correction
    (s a β : ℝ) (D : ℕ) (m : Fin 5 → ℕ)
    (hs : 0 ≤ s) (ha : physical a) (hroot : F s a = 0)
    (hD : ActiveDegree D) (hm : Profile.Valid D m)
    (p : MomentPivots (D/2)) (hp : ValidMomentPivots p) (hβ : 0 < β)
    (R : Compatible a D → GramFamily (D/2))
    (hR : ∀ f, gramPoly a (D/2) p (R f) = f.val)
    (W0 : GramFamily (D/2))
    (hpositive : ∀ b, ((correctedGram (gramCompatible a ha D hD p hp) R
      (normalizedTargetCompatible s a β D m hs ha hroot hm) W0).val b).PosDef) :
    Certificate s a D m := by
  refine ⟨hs,ha,hroot,hD,hm,p,β,
    correctedGram (gramCompatible a ha D hD p hp) R
      (normalizedTargetCompatible s a β D m hs ha hroot hm) W0,
    hp,hβ,hpositive,?_⟩
  exact correctedGram_identity a ha D hD p hp R hR
    (normalizedTargetCompatible s a β D m hs ha hroot hm) W0

#print axioms gramCompatible
#print axioms correctedGram_identity
#print axioms certificate_of_exact_gram_correction
end Blueprint.Thomson.Finite
