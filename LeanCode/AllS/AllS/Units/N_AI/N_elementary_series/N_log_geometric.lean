import Blueprint.CAPContracts
import Blueprint.Target

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP
def logOddPartial (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, x^(2*k+1)/((2*k+1:ℕ):ℝ)
def LogGeometricStatement : Prop :=
  ∀ (x : ℝ) (n : ℕ), 0≤x → x<1 →
    2*logOddPartial (n+1) x ≤ Real.log ((1+x)/(1-x)) ∧
    Real.log ((1+x)/(1-x)) ≤ 2*logOddPartial (n+1) x +
      2*x^(2*n+3)/(((2*n+3:ℕ):ℝ)*(1-x^2))
theorem logHalf_remainder_upper (x : ℝ) (n : ℕ) (hx0 : 0≤x) (hx1 : x<1) :
    1/2*Real.log ((1+x)/(1-x)) ≤ logOddPartial n x +
      x^(2*n+1)/(((2*n+1:ℕ):ℝ)*(1-x^2)) := by
  let F : ℝ→ℝ := fun y => 1/2*Real.log ((1+y)/(1-y)) - logOddPartial n y
  let G : ℝ→ℝ := fun y => y^(2*n+1)/(((2*n+1:ℕ):ℝ)*(1-x^2)) - F y
  have hd : 0<1-x^2 := by nlinarith
  have hk : (0:ℝ)<((2*n+1:ℕ):ℝ) := by positivity
  have hF (y : ℝ) (hy : y∈Set.Icc 0 x) :
      HasDerivAt F ((y^2)^n/(1-y^2)) y := by
    simpa [F, logOddPartial, Nat.cast_add, Nat.cast_mul] using
      Real.hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range n
        (by linarith [hy.1]) (by linarith [hy.2])
  have hG (y : ℝ) (hy : y∈Set.Icc 0 x) :
      HasDerivAt G (y^(2*n)/(1-x^2) - (y^2)^n/(1-y^2)) y := by
    have hp : HasDerivAt
        (fun t : ℝ => t^(2*n+1)/(((2*n+1:ℕ):ℝ)*(1-x^2)))
        (y^(2*n)/(1-x^2)) y := by
      have hraw := ((hasDerivAt_id y).pow (2*n+1)).div_const
        (((2*n+1:ℕ):ℝ)*(1-x^2))
      simpa only [Pi.pow_apply, id_eq, Nat.add_sub_cancel, mul_one,
        mul_div_mul_left _ _ (ne_of_gt hk)] using hraw
    exact hp.sub (hF y hy)
  have hmono : MonotoneOn G (Set.Icc 0 x) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x)
      (fun y hy => (hG y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hG y (interior_subset hy)).hasDerivWithinAt)
    intro y hy
    simp only [interior_Icc, Set.mem_Ioo] at hy
    apply sub_nonneg.mpr
    rw [←pow_mul]
    apply div_le_div_of_nonneg_left (pow_nonneg hy.1.le _) hd
    nlinarith
  have h := hmono ⟨le_rfl,hx0⟩ ⟨hx0,le_rfl⟩ hx0
  have hzero : G 0 = 0 := by simp [G, F, logOddPartial]
  rw [hzero] at h
  dsimp [G, F] at h
  linarith

theorem elementary_series_log_geometric : LogGeometricStatement := by
  intro x n hx0 hx1
  have hl : logOddPartial (n+1) x ≤ 1/2*Real.log ((1+x)/(1-x)) := by
    simpa [logOddPartial, Nat.cast_add, Nat.cast_mul] using
      Real.sum_range_le_log_div hx0 hx1 (n+1)
  have hu := logHalf_remainder_upper x (n+1) hx0 hx1
  have heq : 2*(n+1)+1=2*n+3 := by omega
  rw [heq] at hu
  constructor
  · linarith
  · have hu' : Real.log ((1+x)/(1-x)) ≤ 2*logOddPartial (n+1) x +
        2*(x^(2*n+3)/(((2*n+3:ℕ):ℝ)*(1-x^2))) := by linarith
    convert hu' using 1 <;> ring
#check elementary_series_log_geometric
#print LogGeometricStatement
#print axioms elementary_series_log_geometric
#print axioms logHalf_remainder_upper
end Blueprint.CAP
