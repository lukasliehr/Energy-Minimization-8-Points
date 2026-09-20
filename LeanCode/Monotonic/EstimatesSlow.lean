import LeanCode.Monotonic.Definitions
/-! Scaled reciprocal remainder bounds. The rational bounds are slightly
weaker than those in the paper, while retaining all strict final margins. -/

noncomputable section
open Real Set
namespace SquareAntiprismCounterexample

lemma slow_error_one (t : ℝ) (ht : 0 < t) (ht4 : t ≤ 4) :
    |10000^3 * (-1 / (10000+t)^2) + 10000 - 2*t| ≤ 1/200 := by
  have hd : 0 < (10000+t)^2 := sq_pos_of_pos (by linarith)
  have ht2 : t^2 ≤ 16 := by nlinarith
  have ht3 : t^3 ≤ 64 := by nlinarith [mul_le_mul_of_nonneg_left ht2 ht.le]
  have heq : 10000^3 * (-1 / (10000+t)^2) + 10000 - 2*t =
      -(t^2 * (30000+2*t)) / (10000+t)^2 := by field_simp; ring
  rw [heq, abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hd.le)]
  rw [neg_div, neg_neg, div_le_iff₀ hd]
  nlinarith

lemma slow_error_two (t : ℝ) (ht : 0 < t) (ht4 : t ≤ 4) :
    |10000^3 * (2 / (10000+t)^3) - 2| ≤ 1/400 := by
  have hd : 0 < (10000+t)^3 := pow_pos (by linarith) _
  have ht2 : t^2 ≤ 16 := by nlinarith
  have ht3 : t^3 ≤ 64 := by nlinarith [mul_le_mul_of_nonneg_left ht2 ht.le]
  have heq : 10000^3 * (2 / (10000+t)^3) - 2 =
      -(2*t*(300000000+30000*t+t^2)) / (10000+t)^3 := by field_simp; ring
  rw [heq, abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hd.le)]
  rw [neg_div, neg_neg, div_le_iff₀ hd]
  nlinarith

end SquareAntiprismCounterexample
