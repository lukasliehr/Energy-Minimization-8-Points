import AllS.Units.N_GI.N_continuous_annulus.N_log_derivative

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem exp_cubic_lower (x : ℝ) : 1+x+x^2/2+x^3/6 ≤ exp x := by
  let f2 : ℝ→ℝ := fun t=>exp t-1-t-t^2/2
  let f3 : ℝ→ℝ := fun t=>exp t-1-t-t^2/2-t^3/6
  have hd2 (t : ℝ) : HasDerivAt f2 (exp t-1-t) t := by
    convert! (((Real.hasDerivAt_exp t).sub_const 1).sub (hasDerivAt_id t)).sub
      (((hasDerivAt_id t).pow 2).div_const 2) using 1 <;> dsimp [f2] <;> ring
  have hd3 (t : ℝ) : HasDerivAt f3 (f2 t) t := by
    convert! (hd2 t).sub (((hasDerivAt_id t).pow 3).div_const 6) using 1 <;> dsimp [f2,f3] <;> ring
  have hm2 : Monotone f2 := monotone_of_deriv_nonneg (fun t=>(hd2 t).differentiableAt) (by
    intro t
    rw [(hd2 t).deriv]
    linarith [Real.add_one_le_exp t])
  have hz2 : f2 0=0 := by simp [f2]
  have hz3 : f3 0=0 := by simp [f3]
  have hmin : 0≤f3 x := by
    rcases le_total 0 x with hx|hx
    · have hm : MonotoneOn f3 (Set.Ici 0) := monotoneOn_of_deriv_nonneg (convex_Ici 0)
        (fun t _=>(hd3 t).continuousAt.continuousWithinAt)
        (fun t _=>(hd3 t).differentiableAt.differentiableWithinAt) (by
          intro t ht
          rw [interior_Ici] at ht
          rw [(hd3 t).deriv]
          have h := hm2 ht.le
          rwa [hz2] at h)
      have h := hm (by simp) hx hx
      rwa [hz3] at h
    · have hm : AntitoneOn f3 (Set.Iic 0) := antitoneOn_of_deriv_nonpos (convex_Iic 0)
        (fun t _=>(hd3 t).continuousAt.continuousWithinAt)
        (fun t _=>(hd3 t).differentiableAt.differentiableWithinAt) (by
          intro t ht
          rw [interior_Iic] at ht
          rw [(hd3 t).deriv]
          have h := hm2 ht.le
          rwa [hz2] at h)
      have h := hm hx (by simp) hx
      rwa [hz3] at h
  dsimp [f3] at hmin
  linarith

theorem massOne_cubic_lower (W v : ℝ) (hW : 1<W) (hv : 0≤v) :
    W+v^2/2-v^3/6 ≤ twoValueExp W v 1 := by
  obtain ⟨hA,hB,hbal,h1,h2,hC⟩ := twoValue_coefficients W 1 (by norm_num) hW
  simp only [one_mul,mul_one] at hbal h1
  have hsum : (twoValueA W 1)^2+(W-1)*(twoValueB W 1)^2=1 := by
    linear_combination h1-twoValueB W 1*hbal
  have hAs : (twoValueA W 1)^2=(W-1)/W := by
    unfold twoValueA
    simp only [mul_one]
    exact Real.sq_sqrt (by positivity)
  have hAle : twoValueA W 1≤1 := by
    have hdiv : (W-1)/W<1 := (div_lt_one (by linarith)).mpr (by linarith)
    nlinarith
  have hAcube : (twoValueA W 1)^3≤1 := by
    calc
      _ ≤ (1:ℝ)^3 := by gcongr
      _ = _ := by norm_num
  have hl := exp_cubic_lower (-v*twoValueA W 1)
  have hu := mul_le_mul_of_nonneg_left (exp_cubic_lower (v*twoValueB W 1)) (by linarith : 0≤W-1)
  have hc := mul_nonneg (sub_nonneg.mpr hAcube) (pow_nonneg hv 3)
  have hpos : 0≤(W-1)*(v*twoValueB W 1)^3 := by positivity
  change W+v^2/2-v^3/6≤1*exp (-v*twoValueA W 1)+(W-1)*exp (v*twoValueB W 1)
  have hs := congrArg (fun t : ℝ=>t*v^2) hsum
  have hb := congrArg (fun t : ℝ=>t*v) hbal
  nlinarith

#print axioms exp_cubic_lower
#print axioms massOne_cubic_lower
end Blueprint.Thomson.Tail.Implementation
