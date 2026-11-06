import AllS.Units.N_GI.N_weighted_two_value.N_constraint_compact

noncomputable section
open Real
open scoped BigOperators
namespace Blueprint.Thomson.Tail.Implementation

def weightedDot {n : ℕ} (w x y : Fin n → ℝ) : ℝ := ∑ i, w i*x i*y i

theorem weightedDot_comm {n : ℕ} (w x y : Fin n → ℝ) : weightedDot w x y=weightedDot w y x := by
  unfold weightedDot
  apply Finset.sum_congr rfl
  intro i _; ring

theorem weightedDot_self {n : ℕ} (w x : Fin n → ℝ) : weightedDot w x x=weightedSquare w x := by
  unfold weightedDot weightedSquare
  apply Finset.sum_congr rfl
  intro i _; ring

theorem weightedMean_linear {n : ℕ} (w x y : Fin n → ℝ) (a b : ℝ) :
    weightedMean w (fun i => a*x i+b*y i)=a*weightedMean w x+b*weightedMean w y := by
  simp only [weightedMean,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _; ring

theorem weightedSquare_linear {n : ℕ} (w x y : Fin n → ℝ) (a b : ℝ) :
    weightedSquare w (fun i => a*x i+b*y i)=
      a^2*weightedSquare w x+2*a*b*weightedDot w x y+b^2*weightedSquare w y := by
  simp only [weightedSquare,weightedDot,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _; ring

theorem weightedSquare_zero {n : ℕ} (w x : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hz : weightedSquare w x=0) : ∀ i, x i=0 := by
  intro i
  have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
    mul_nonneg (hw j).le (sq_nonneg (x j))) (Finset.mem_univ i)
  change w i*(x i)^2 ≤ weightedSquare w x at h
  rw [hz] at h
  have he : w i*(x i)^2=0 := le_antisymm h (mul_nonneg (hw i).le (sq_nonneg _))
  have hx : (x i)^2=0 := (mul_eq_zero.mp he).resolve_left (hw i).ne'
  nlinarith

#print axioms weightedSquare_linear
#print axioms weightedSquare_zero
end Blueprint.Thomson.Tail.Implementation
