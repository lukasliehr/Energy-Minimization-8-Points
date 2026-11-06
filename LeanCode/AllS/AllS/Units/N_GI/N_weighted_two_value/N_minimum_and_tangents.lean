import AllS.Units.N_GI.N_weighted_two_value.N_tangent_variation

noncomputable section
open Real
open scoped BigOperators
namespace Blueprint.Thomson.Tail.Implementation

theorem weightedMean_affine_sub {n : ℕ} (w x y : Fin n → ℝ) (a b : ℝ) :
    weightedMean w (fun i => y i-a-b*x i)=weightedMean w y-a*(∑ i,w i)-b*weightedMean w x := by
  simp only [weightedMean,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _; ring

theorem weightedDot_affine_sub {n : ℕ} (w x y : Fin n → ℝ) (a b : ℝ) :
    weightedDot w x (fun i => y i-a-b*x i)=weightedDot w x y-a*weightedMean w x-b*weightedSquare w x := by
  simp only [weightedMean,weightedDot,weightedSquare,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _; ring

theorem weightedDot_affine_add {n : ℕ} (w x u : Fin n → ℝ) (a b : ℝ) :
    weightedDot w (fun i => u i+a+b*x i) u=weightedSquare w u+a*weightedMean w u+b*weightedDot w x u := by
  simp only [weightedMean,weightedDot,weightedSquare,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _; ring

theorem weighted_total_pos {n : ℕ} (hn : 2 ≤ n) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) : 0 < ∑ i,w i := by
  let i : Fin n := ⟨0,by omega⟩
  have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => (hw j).le) (Finset.mem_univ i)
  exact lt_of_lt_of_le (hw i) h

theorem weighted_minimum_affine_exp {n : ℕ} (hn : 2 ≤ n) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (v : ℝ) (hv : 0 < v) (x : Fin n → ℝ)
    (hx : x ∈ weightedFeasible w v) (hmin : IsMinOn (weightedExp w) (weightedFeasible w v) x) :
    ∃ a b : ℝ, ∀ i, exp (x i)=a+b*x i := by
  let y : Fin n → ℝ := fun i => exp (x i)
  let W := ∑ i,w i
  let a := weightedMean w y/W
  let b := weightedDot w x y/v^2
  let u : Fin n → ℝ := fun i => y i-a-b*x i
  have hW : 0 < W := weighted_total_pos hn w hw
  have ha : a*W=weightedMean w y := div_mul_cancel₀ _ hW.ne'
  have hb : b*v^2=weightedDot w x y := div_mul_cancel₀ _ (pow_ne_zero 2 hv.ne')
  have hum : weightedMean w u=0 := by
    change weightedMean w (fun i => y i-a-b*x i)=0
    rw [weightedMean_affine_sub,hx.1,mul_zero,sub_zero]
    exact sub_eq_zero.mpr ha.symm
  have hux : weightedDot w x u=0 := by
    change weightedDot w x (fun i => y i-a-b*x i)=0
    rw [weightedDot_affine_sub,hx.1,hx.2,mul_zero,sub_zero]
    exact sub_eq_zero.mpr hb.symm
  have hz := weighted_tangent_first_variation w hw v hv x hx hmin u hum hux
  change weightedDot w y u=0 at hz
  have hy : y=(fun i => u i+a+b*x i) := by ext i; dsimp [u]; ring
  rw [hy,weightedDot_affine_add,hum,hux,mul_zero,mul_zero,add_zero,add_zero] at hz
  have hu := weightedSquare_zero w u hw hz
  refine ⟨a,b,?_⟩
  intro i
  have h := hu i
  change exp (x i)-a-b*x i=0 at h
  linarith

theorem weighted_two_value_minimum_and_tangents {n : ℕ} (hn : 2 ≤ n) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (v : ℝ) (hv : 0 < v) :
    ∃ x ∈ weightedFeasible w v, IsMinOn (weightedExp w) (weightedFeasible w v) x ∧
      ∃ a b : ℝ, ∀ i, exp (x i)=a+b*x i := by
  obtain ⟨hK,hcomp⟩ := weighted_two_value_constraint_compact hn w hw v hv
  obtain ⟨x,hx,hmin⟩ := hcomp.exists_isMinOn hK (weightedExp_continuous w).continuousOn
  exact ⟨x,hx,hmin,weighted_minimum_affine_exp hn w hw v hv x hx hmin⟩

#check weighted_two_value_minimum_and_tangents
#print axioms weighted_two_value_minimum_and_tangents
end Blueprint.Thomson.Tail.Implementation
