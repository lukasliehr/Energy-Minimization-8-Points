import Lean_Code.ContactArcLocalGeometry

set_option maxHeartbeats 1500000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Denominator and oriented numerator of the half-solid-angle formula.
They will provide a finite angle-sum separation function for graph cycles. -/
def solidAngleDenom (p a b : ℝ³) : ℝ :=
  1 + inner ℝ a b + inner ℝ p a + inner ℝ p b

def solidAngleNumer (p a b : ℝ³) : ℝ := inner ℝ (crossVec a b) p

lemma solidAngle_norm_identity (p a b : ℝ³) (hp : ‖p‖ = 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    solidAngleDenom p a b ^ 2 + solidAngleNumer p a b ^ 2 =
      2 * (1 + inner ℝ a b) * (1 + inner ℝ p a) * (1 + inner ℝ p b) := by
  have h := unit_triple_gram_identity a b p ha hb hp
  rw [real_inner_comm p a, real_inner_comm p b] at h
  unfold solidAngleDenom solidAngleNumer
  rw [h]
  ring

/-- The differential of one edge's solid angle is a difference of endpoint
terms. Summing along a closed cycle will therefore telescope. This identity
is purely algebraic and also covers coplanar and zero-numerator cases. -/
lemma solidAngle_tangent_numerator (p a b h : ℝ³)
    (hp : ‖p‖ = 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hph : inner ℝ p h = 0) :
    solidAngleDenom p a b * inner ℝ (crossVec a b) h -
      solidAngleNumer p a b * (inner ℝ a h + inner ℝ b h) =
    (1 + inner ℝ a b) *
      ((1 + inner ℝ p a) * inner ℝ (crossVec p b) h -
        (1 + inner ℝ p b) * inner ℝ (crossVec p a) h) := by
  have hr := triple_cramer p a b h
  rw [triple_cyclic p a b] at hr
  have h0 := congrArg (fun x : ℝ³ => inner ℝ p x) hr
  have h1 := congrArg (fun x : ℝ³ => inner ℝ (a + b) x) hr
  have hbpc : inner ℝ (crossVec b p) h = -inner ℝ (crossVec p b) h := by
    rw [crossVec_swap p b, inner_neg_left]
  simp only [inner_smul_right, inner_add_right, inner_add_left,
    real_inner_self_eq_norm_sq, hp, ha, hb, hph, one_pow, mul_one, mul_zero,
    real_inner_comm p a, real_inner_comm p b, real_inner_comm a b, hbpc] at h0 h1
  unfold solidAngleDenom solidAngleNumer
  linear_combination -h1 - (1 + inner ℝ a b) * h0

end SquareAntiprismVerification
