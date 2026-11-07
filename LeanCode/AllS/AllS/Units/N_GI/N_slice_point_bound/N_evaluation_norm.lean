import AllS.Units.N_GI.N_slice_point_bound.N_projection_block

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem localSliceProjection_norm_bound (i : Fin 8) (u v : ℝ) :
    ‖sliceProjection (localEvaluation i u v)‖^2 ≤ (1-√2/8)*(u^2+v^2) := by
  rw [sliceProjection_norm_sq,localEvaluation_norm_sq,local_rotation_projection_sq]
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hp := Real.sqrt_nonneg (2:ℝ)
  have hlt : √(2:ℝ)<3/2 := by nlinarith
  nlinarith [sq_nonneg v]

theorem slice_point_bound_evaluation_norm (q : TangentCoordinates) (hq : q∈rotationSlice) (i : Fin 8) :
    ‖tangentVector q i‖^2 ≤ (1-√2/8)*‖q‖^2 := by
  let v := localEvaluation i (q (i,0)) (q (i,1))
  have hi : inner ℝ q v=(q (i,0))^2+(q (i,1))^2 := by
    rw [localEvaluation_inner]
    ring
  have hs : inner ℝ q (sliceProjection v)=inner ℝ q v := sliceProjection_inner q v hq
  have hnorm := localSliceProjection_norm_bound i (q (i,0)) (q (i,1))
  change ‖sliceProjection v‖^2 ≤ _ at hnorm
  have hc : (inner ℝ q (sliceProjection v))^2 ≤ ‖q‖^2*‖sliceProjection v‖^2 := by
    have h := abs_real_inner_le_norm q (sliceProjection v)
    nlinarith [sq_abs (inner ℝ q (sliceProjection v)),abs_nonneg (inner ℝ q (sliceProjection v)),
      norm_nonneg q,norm_nonneg (sliceProjection v)]
  rw [hs,hi] at hc
  have hm := mul_le_mul_of_nonneg_left hnorm (sq_nonneg ‖q‖)
  rw [tangentVector_norm_sq]
  have hcoef : 0 ≤ 1-√(2:ℝ)/8 := by
    have hh := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    nlinarith [Real.sqrt_nonneg (2:ℝ)]
  have hB : 0 ≤ (1-√(2:ℝ)/8)*‖q‖^2 := mul_nonneg hcoef (sq_nonneg _)
  have hscalar : ∀ A B : ℝ, 0 ≤ A → 0 ≤ B → A^2 ≤ B*A → A ≤ B := by
    intro A B hA hB hh
    nlinarith
  apply hscalar _ _ (by positivity) hB
  calc
    _ ≤ ‖q‖^2*‖sliceProjection v‖^2 := hc
    _ ≤ ‖q‖^2*((1-√2/8)*((q (i,0))^2+(q (i,1))^2)) := hm
    _ = _ := by ring

#print axioms slice_point_bound_evaluation_norm
end Blueprint.Thomson.Tail.Implementation
