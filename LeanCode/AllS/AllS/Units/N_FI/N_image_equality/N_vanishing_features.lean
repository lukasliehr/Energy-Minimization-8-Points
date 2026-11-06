import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

def VanishingFeaturesContract : Prop := ∀ n N : ℕ,
  ∀ W : Matrix (Fin n) (Fin n) ℝ,W.PosDef → ∀ w : Fin N → ℝ,
  ∀ v : Fin N → Fin n → ℝ,(∀ t,0 ≤ w t) →
  (∑ t,w t*dotProduct (v t) (W.mulVec (v t)))=0 → ∀ t,w t=0 ∨ v t=0

theorem image_equality_vanishing_features : VanishingFeaturesContract := by
  intro n N W hW w v hw hsum t
  have hn (r : Fin N) : 0 ≤ w r*dotProduct (v r) (W.mulVec (v r)) :=
    mul_nonneg (hw r) (by simpa only [star_trivial] using hW.posSemidef.dotProduct_mulVec_nonneg (v r))
  have hz : w t*dotProduct (v t) (W.mulVec (v t))=0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun r hr => hn r)).mp hsum t (Finset.mem_univ _)
  by_cases hwt : w t=0
  · exact Or.inl hwt
  · right
    by_contra hvt
    have hwpos : 0<w t := lt_of_le_of_ne (hw t) (Ne.symm hwt)
    have hvpos : 0<dotProduct (v t) (W.mulVec (v t)) := by
      simpa only [star_trivial] using hW.dotProduct_mulVec_pos hvt
    exact (ne_of_gt (mul_pos hwpos hvpos)) hz

#check image_equality_vanishing_features
#print axioms image_equality_vanishing_features
end Blueprint.Thomson.Finite
