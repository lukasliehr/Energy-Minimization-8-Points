import AllS.Units.N_GI.N_signed_mean.N_stress_identity
import AllS.Units.N_GI.N_contact_taylor.N_remainder_helpers

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def chartQuarticError (q : TangentCoordinates) (i : Fin 8) : ℝ :=
  -‖tangentVector q i‖^4/(2*(1+chartRoot q i)^2)

theorem chartNormalDisplacement_split (q : TangentCoordinates) (hq : ‖q‖ < 1) (i : Fin 8) :
    chartNormalDisplacement q i= -‖tangentVector q i‖^2/2+chartQuarticError q i := by
  have hs := chartRoot_sq q hq i
  have hn : 0 ≤ chartRoot q i := Real.sqrt_nonneg _
  unfold chartNormalDisplacement chartQuarticError
  field_simp
  nlinarith [sq_nonneg ((chartRoot q i)^2+‖tangentVector q i‖^2-1)]

theorem euclidean_norm_le_sum_abs {ι : Type*} [Fintype ι] (z : EuclideanSpace ℝ ι) :
    ‖z‖ ≤ ∑i, |z i| := by
  have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := (Finset.univ : Finset ι))
    (f := fun i=>|z i|) (fun i _=>abs_nonneg (z i))
  simp only [sq_abs,← EuclideanSpace.real_norm_sq_eq] at h
  have hn : 0 ≤ ∑i,|z i| := Finset.sum_nonneg (fun i _=>abs_nonneg (z i))
  nlinarith [norm_nonneg z]

theorem chartNormalDisplacement_abs (q : TangentCoordinates) (hq : ‖q‖ < 1) (i : Fin 8) :
    |chartNormalDisplacement q i| ≤ ‖tangentVector q i‖^2/(1+√(1-‖q‖^2)) := by
  have hi := (chartRoot_bounds q hq i).2.2
  have hs := chartRoot_scaled_loss q hq i
  rw [chartNormalDisplacement,abs_of_nonpos (by linarith)]
  apply (le_div_iff₀ (by positivity)).mpr
  linarith

theorem chartQuarticError_abs (q : TangentCoordinates) (hq : ‖q‖ < 1) (i : Fin 8) :
    |chartQuarticError q i| ≤ ‖tangentVector q i‖^4/(2*(1+√(1-‖q‖^2))^2) := by
  have hs := (chartRoot_bounds q hq i).2.1
  unfold chartQuarticError
  rw [abs_div,abs_neg,abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith [Real.sqrt_nonneg (1-‖q‖^2)]

theorem tangentVector_sum_fourth (q : TangentCoordinates) :
    (∑i,‖tangentVector q i‖^4) ≤ ‖q‖^4 := by
  have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := (Finset.univ : Finset (Fin 8)))
    (f := fun i=>‖tangentVector q i‖^2) (fun i _=>sq_nonneg ‖tangentVector q i‖)
  simpa only [← pow_mul,tangentVector_sum_norm_sq] using h

theorem chartNormalDisplacement_norm (q : TangentCoordinates) (hq : ‖q‖ < 1) :
    ‖(WithLp.toLp 2 (chartNormalDisplacement q) : EuclideanSpace ℝ (Fin 8))‖ ≤
      ‖q‖^2/(1+√(1-‖q‖^2)) := by
  refine (euclidean_norm_le_sum_abs _).trans ?_
  calc
    _ ≤ ∑i,‖tangentVector q i‖^2/(1+√(1-‖q‖^2)) := by
      exact Finset.sum_le_sum (fun i _=>chartNormalDisplacement_abs q hq i)
    _ = _ := by rw [← Finset.sum_div,tangentVector_sum_norm_sq]

theorem chartQuarticError_norm (q : TangentCoordinates) (hq : ‖q‖ < 1) :
    ‖(WithLp.toLp 2 (chartQuarticError q) : EuclideanSpace ℝ (Fin 8))‖ ≤
      ‖q‖^4/(2*(1+√(1-‖q‖^2))^2) := by
  refine (euclidean_norm_le_sum_abs _).trans ?_
  calc
    _ ≤ ∑i,‖tangentVector q i‖^4/(2*(1+√(1-‖q‖^2))^2) := by
      exact Finset.sum_le_sum (fun i _=>chartQuarticError_abs q hq i)
    _ ≤ _ := by
      rw [← Finset.sum_div]
      exact div_le_div_of_nonneg_right (tangentVector_sum_fourth q) (by positivity)

#print axioms chartNormalDisplacement_split
#print axioms chartNormalDisplacement_norm
#print axioms chartQuarticError_norm
end Blueprint.Thomson.Tail.Implementation
