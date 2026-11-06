import AllS.Units.N_GI.N_cycle34.N_triangle

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem force_cot_sq_lower (m : ℝ) (hm : 0 < m) (hmmax : m ≤ 29/20) :
    51/29 ≤ ((tan (forceAngle m/2))⁻¹)^2 := by
  let v := forceAngle m/2
  obtain ⟨hx,hx1,hy,hx2,_,_⟩ := force_trig_parameters m hm hmmax
  have hv := force_v_range m hm hmmax
  have hs : 0 < sin v := Real.sin_pos_of_pos_of_lt_pi hv.1 (by dsimp [v]; linarith [hv.2,Real.pi_pos])
  change 51/29 ≤ ((tan v)⁻¹)^2
  rw [Real.tan_eq_sin_div_cos,inv_div,div_pow]
  apply (le_div_iff₀ (sq_pos_of_pos hs)).mpr
  change cos v^2=1-m/4 at hx2
  nlinarith [Real.sin_sq_add_cos_sq v]

theorem force_quad_triple (v : ℝ) (hv0 : 0 < v) (hv1 : v < π/4) :
    let b := tan ((π-v)/3)
    1 < b ∧ b < sqrt 3 ∧ (tan v)⁻¹*b*(3-b^2)=3*b^2-1 := by
  let β := (π-v)/3
  have hβ : π/4 < β ∧ β < π/3 := by dsimp [β]; constructor <;> linarith
  have hb1 : 1 < tan β := by
    have h := Real.strictMonoOn_tan
      (show π/4 ∈ Set.Ioo (-(π/2)) (π/2) by constructor <;> linarith [Real.pi_pos])
      (show β ∈ Set.Ioo (-(π/2)) (π/2) by constructor <;> linarith [Real.pi_pos,hβ.1,hβ.2]) hβ.1
    simpa using h
  have hb3 : tan β < sqrt 3 := by
    have h := Real.strictMonoOn_tan
      (show β ∈ Set.Ioo (-(π/2)) (π/2) by constructor <;> linarith [Real.pi_pos,hβ.1,hβ.2])
      (show π/3 ∈ Set.Ioo (-(π/2)) (π/2) by constructor <;> linarith [Real.pi_pos]) hβ.2
    simpa using h
  have hs : 0 < sin v := Real.sin_pos_of_pos_of_lt_pi hv0 (by linarith [Real.pi_pos])
  have hc : 0 < cos β := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,hβ.1],by linarith [Real.pi_pos,hβ.2]⟩
  have hs3 := Real.sin_three_mul β
  have hc3 := Real.cos_three_mul β
  rw [show 3*β=π-v by dsimp [β]; ring,Real.sin_pi_sub] at hs3
  rw [show 3*β=π-v by dsimp [β]; ring,Real.cos_pi_sub] at hc3
  have hsq := Real.sin_sq_add_cos_sq β
  have hsv : sin v=sin β*(3*cos β^2-sin β^2) := by
    linear_combination hs3-3*sin β*hsq
  have hcv : cos v=cos β*(3*sin β^2-cos β^2) := by
    linear_combination -hc3-3*cos β*hsq
  refine ⟨hb1,hb3,?_⟩
  change (tan v)⁻¹*tan β*(3-tan β^2)=3*tan β^2-1
  rw [Real.tan_eq_sin_div_cos,inv_div,Real.tan_eq_sin_div_cos]
  field_simp [hs.ne',hc.ne']
  rw [hsv,hcv]
  ring

theorem cycle34_quad_polynomial (m : ℝ) (hm : 0 < m) (hmmax : m ≤ 29/20) :
    let v := forceAngle m/2
    let q := tan ((π-v)/3)^2
    1 < q ∧ q < 3 ∧ 6/5 ≤ q := by
  let v := forceAngle m/2
  let b := tan ((π-v)/3)
  let q := b^2
  have hv := force_v_range m hm hmmax
  obtain ⟨hb1,hb3,hrel⟩ := force_quad_triple v hv.1 hv.2
  have hq1 : 1 < q := by dsimp [q,b]; nlinarith
  have hq3 : q < 3 := by
    have hr := Real.sq_sqrt (show (0:ℝ)≤3 by norm_num)
    dsimp [q,b]
    nlinarith
  have ht := force_cot_sq_lower m hm hmmax
  have he : ((tan v)⁻¹)^2*q*(3-q)^2=(3*q-1)^2 := by
    have h := congrArg (fun x : ℝ => x^2) hrel
    simpa only [mul_pow,q,b] using h
  have hnonneg : 0 ≤ q*(3-q)^2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hineq : 845*q*(3-q)^2 ≤ 486*(3*q-1)^2 := by
    have hbnd : (845/486:ℝ) ≤ ((tan v)⁻¹)^2 := le_trans (by norm_num) ht
    have hmul := mul_le_mul_of_nonneg_right hbnd hnonneg
    nlinarith [he]
  have hid : 486*(3*q-1)^2-845*q*(3-q)^2=(5*q-6)*(-169*q^2+1686*q-81) := by ring
  have hpos : 0 < -169*q^2+1686*q-81 := by
    have hh := mul_nonneg (show 0 ≤ q by linarith) (show 0 ≤ 3-q by linarith)
    nlinarith
  have hprod : 0 ≤ (5*q-6)*(-169*q^2+1686*q-81) := by rw [← hid]; linarith
  have hfin := nonneg_of_mul_nonneg_left hprod hpos
  refine ⟨hq1,hq3,?_⟩
  change 6/5 ≤ q
  linarith

#check cycle34_quad_polynomial
#print axioms cycle34_quad_polynomial
end Blueprint.Thomson.Tail.Implementation
