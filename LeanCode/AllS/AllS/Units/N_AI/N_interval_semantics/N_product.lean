import AllS.Units.N_AI.N_interval_semantics.N_affine
import Blueprint.Target

namespace Blueprint.CAP
def IntervalProductStatement : Prop :=
  ∀ {I J K : Box} {x y : ℝ}, I.WellFormed → J.WellFormed → K.WellFormed →
    I.Contains x → J.Contains y → Box.MulGate I J K → K.Contains (x*y)
private theorem real_mul_between (l u x z kl ku : ℝ) (hx : l≤x ∧ x≤u)
    (hl : kl≤l*z ∧ l*z≤ku) (hu : kl≤u*z ∧ u*z≤ku) : kl≤x*z ∧ x*z≤ku := by
  rcases le_total 0 z with hz | hz
  · exact ⟨hl.1.trans (mul_le_mul_of_nonneg_right hx.1 hz),
      (mul_le_mul_of_nonneg_right hx.2 hz).trans hu.2⟩
  · exact ⟨hu.1.trans (mul_le_mul_of_nonpos_right hx.2 hz),
      (mul_le_mul_of_nonpos_right hx.1 hz).trans hl.2⟩

theorem Box.contains_mul {I J K : Box} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) (hg : I.MulGate J K) :
    K.Contains (x*y) := by
  have corners (a : ℚ) (ha : a∈({I.lo,I.hi}:Finset ℚ))
      (b : ℚ) (hb : b∈({J.lo,J.hi}:Finset ℚ)) :
      (K.lo:ℝ)≤(a:ℝ)*(b:ℝ) ∧ (a:ℝ)*(b:ℝ)≤(K.hi:ℝ) := by
    constructor
    · exact_mod_cast (hg a ha b hb).1
    · exact_mod_cast (hg a ha b hb).2
  have lower : (K.lo:ℝ)≤(I.lo:ℝ)*y ∧ (I.lo:ℝ)*y≤(K.hi:ℝ) := by
    simpa only [mul_comm] using
      real_mul_between J.lo J.hi y I.lo K.lo K.hi hy
        (by simpa only [mul_comm] using corners I.lo (by simp) J.lo (by simp))
        (by simpa only [mul_comm] using corners I.lo (by simp) J.hi (by simp))
  have upper : (K.lo:ℝ)≤(I.hi:ℝ)*y ∧ (I.hi:ℝ)*y≤(K.hi:ℝ) := by
    simpa only [mul_comm] using
      real_mul_between J.lo J.hi y I.hi K.lo K.hi hy
        (by simpa only [mul_comm] using corners I.hi (by simp) J.lo (by simp))
        (by simpa only [mul_comm] using corners I.hi (by simp) J.hi (by simp))
  exact real_mul_between I.lo I.hi x y K.lo K.hi hx lower upper

theorem interval_semantics_product : IntervalProductStatement := by
  intro I J K x y _ _ _ hx hy hg
  exact Box.contains_mul hx hy hg
#check interval_semantics_product
#print interval_semantics_product
#print axioms interval_semantics_product
end Blueprint.CAP
