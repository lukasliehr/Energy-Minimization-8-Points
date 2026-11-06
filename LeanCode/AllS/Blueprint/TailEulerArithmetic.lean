import Mathlib

noncomputable section
open Real
open scoped BigOperators
namespace Blueprint.TailEulerArithmetic

/-- A concave function with equal endpoint values lies above that value. -/
theorem concave_endpoint_lower {f : ℝ → ℝ} {a b x L : ℝ}
    (hab : a ≤ b) (hf : ConcaveOn ℝ (Set.Icc a b) f)
    (ha : f a = L) (hb : f b = L) (hx : x ∈ Set.Icc a b) : L ≤ f x := by
  have h := hf.min_le_of_mem_Icc (show a ∈ Set.Icc a b from ⟨le_rfl, hab⟩)
    (show b ∈ Set.Icc a b from ⟨hab, le_rfl⟩) hx
  simpa [ha, hb] using h

/-- Exact Euler count from the angle sum, the weak permutation Euler bound,
and the elementary rhombus excess lower bound. No planar topology is assumed. -/
theorem euler_count_of_excess (T Q E : ℕ) (α S₄ : ℝ)
    (hD : 3 * T + 4 * Q = 2 * E)
    (hweak : 12 ≤ T + 2 * Q)
    (hα : 2 * Real.pi / 5 < α)
    (hquad : 2 * (Q : ℝ) * (3 * α - Real.pi) ≤ S₄)
    (htotal : (T : ℝ) * (3 * α - Real.pi) + S₄ =
      (16 - ((T : ℝ) + 2 * (Q : ℝ))) * Real.pi) :
    T + 2 * Q = 12 := by
  have hbound : 3 * ((T : ℝ) + 2 * (Q : ℝ)) * α ≤ 16 * Real.pi := by
    nlinarith
  have hαpos : 0 < α := by linarith [Real.pi_pos]
  have hlt : T + 2 * Q < 14 := by
    by_contra hn
    have h14 : 14 ≤ T + 2 * Q := by omega
    have h14r : (14 : ℝ) ≤ (T : ℝ) + 2 * (Q : ℝ) := by exact_mod_cast h14
    have hm := mul_le_mul_of_nonneg_right h14r hαpos.le
    nlinarith [Real.pi_pos]
  omega

#print axioms concave_endpoint_lower
#print axioms euler_count_of_excess

end Blueprint.TailEulerArithmetic
