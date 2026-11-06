import AllS.Units.N_AI.N_fixed_tables.GramCombinationSupport
import AllS.Units.N_FI.N_raw_projection.N_target_directions
import AllS.Units.N_F.N_quotient
import AllS.Units.N_F.N_compatibility

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

/-- A coordinate source identified with the actual Gram polynomial gives its
    canonical retained coordinates, without computing an inverse substitution. -/
theorem fixedGram_retained_of_source (a : ℝ) (ha : physical a) (d : ℕ)
    (hl : 6≤d) (hu : d≤9) (p : MomentPivots d) (hp : ValidMomentPivots p)
    (W : GramFamily d) (q : Poly3) (hq : invariantSubst q=gramPoly a d p W)
    (t : RetainedIndex (2*d)) :
    retainCompatible a (2*d) ⟨gramPoly a d p W,gramPoly_compatible a ha d hl hu p hp W⟩ t=
      MvPolynomial.coeff (tagExponent t.val) q :=
  retained_coordinates_of_invariantSubst (2*d)
    (compatibleToBounded a (2*d) ⟨gramPoly a d p W,gramPoly_compatible a ha d hl hu p hp W⟩)
    q hq t

/-- Exact source-coordinate recovery upgrades to full polynomial equality using
    the already proved compatible-coordinate quotient. -/
theorem fixedGram_full_recovery_of_source (a : ℝ) (ha : physical a) (d : ℕ)
    (hl : 6≤d) (hu : d≤9) (p : MomentPivots d) (hp : ValidMomentPivots p)
    (W : GramFamily d) (f : Compatible a (2*d)) (q : Poly3)
    (hq : invariantSubst q=gramPoly a d p W)
    (hc : ∀ t : RetainedIndex (2*d),
      MvPolynomial.coeff (tagExponent t.val) q=retainCompatible a (2*d) f t) :
    gramPoly a d p W=f.val := by
  have he : (⟨gramPoly a d p W,gramPoly_compatible a ha d hl hu p hp W⟩ : Compatible a (2*d))=f := by
    apply (compatible_coordinate_quotient a ha (2*d) (by omega)).injective
    funext t
    exact (fixedGram_retained_of_source a ha d hl hu p hp W q hq t).trans (hc t)
  exact congrArg Subtype.val he

#print axioms fixedGram_retained_of_source
#print axioms fixedGram_full_recovery_of_source
end Blueprint.Thomson.Finite
