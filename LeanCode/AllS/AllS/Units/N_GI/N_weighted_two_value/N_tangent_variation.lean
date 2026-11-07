import AllS.Units.N_GI.N_weighted_two_value.N_weighted_algebra

noncomputable section
open Real Filter
open scoped BigOperators
namespace Blueprint.Thomson.Tail.Implementation

theorem weighted_tangent_first_variation {n : ℕ} (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (v : ℝ) (hv : 0 < v) (x : Fin n → ℝ)
    (hx : x ∈ weightedFeasible w v) (hmin : IsMinOn (weightedExp w) (weightedFeasible w v) x)
    (u : Fin n → ℝ) (hum : weightedMean w u=0) (hux : weightedDot w x u=0) :
    weightedDot w (fun i => exp (x i)) u=0 := by
  by_cases hu0 : weightedSquare w u=0
  · have hz := weightedSquare_zero w u hw hu0
    simp [weightedDot,hz]
  have hup : 0 < weightedSquare w u := lt_of_le_of_ne (weightedSquare_nonneg w u hw) (Ne.symm hu0)
  let c : ℝ := v/√(weightedSquare w u)
  have hspos : 0 < √(weightedSquare w u) := Real.sqrt_pos.mpr hup
  have hc : 0 < c := div_pos hv hspos
  have hc2 : c^2*weightedSquare w u=v^2 := by
    dsimp [c]
    rw [div_pow,Real.sq_sqrt hup.le]
    field_simp
  let γ : ℝ → Fin n → ℝ := fun t i => cos t*x i+(c*sin t)*u i
  have hγ0 : γ 0=x := by ext i; simp [γ]
  have hγmem (t : ℝ) : γ t ∈ weightedFeasible w v := by
    constructor
    · rw [show γ t=(fun i => cos t*x i+(c*sin t)*u i) from rfl,weightedMean_linear,hx.1,hum]
      ring
    · rw [show γ t=(fun i => cos t*x i+(c*sin t)*u i) from rfl,weightedSquare_linear,hx.2,hux]
      have htrig := Real.sin_sq_add_cos_sq t
      linear_combination v^2*htrig+(sin t)^2*hc2
  have hder (i : Fin n) : HasDerivAt (fun t => γ t i) (c*u i) 0 := by
    have h := ((Real.hasDerivAt_cos 0).mul_const (x i)).add
      (((Real.hasDerivAt_sin 0).const_mul c).mul_const (u i))
    convert! h using 1 <;> simp [γ]
  have hexp (i : Fin n) : HasDerivAt (fun t => w i*exp (γ t i))
      (w i*(exp (x i)*(c*u i))) 0 := by
    have h := ((hder i).exp).const_mul (w i)
    simpa only [hγ0] using h
  have hf : HasDerivAt (fun t => weightedExp w (γ t))
      (c*weightedDot w (fun i => exp (x i)) u) 0 := by
    have h := HasDerivAt.fun_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hexp i)
    convert! h using 1
    unfold weightedDot
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _; ring
  have hlocal : IsLocalMin (fun t => weightedExp w (γ t)) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    change weightedExp w (γ 0) ≤ weightedExp w (γ t)
    rw [hγ0]
    exact hmin (hγmem t)
  have hz := hlocal.hasDerivAt_eq_zero hf
  exact (mul_eq_zero.mp hz).resolve_left hc.ne'

#print axioms weighted_tangent_first_variation
end Blueprint.Thomson.Tail.Implementation
