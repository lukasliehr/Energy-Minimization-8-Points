import AllS.Units.N_G.N_cycle_winding

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem force_v_range (m : ℝ) (hm : 0 < m) (hmmax : m ≤ 29/20) :
    0 < forceAngle m/2 ∧ forceAngle m/2 < π/4 := by
  have h0 : 0 < forceAngle m := Real.arccos_pos.mpr (by linarith)
  have h1 : forceAngle m < π/2 := Real.arccos_lt_pi_div_two.mpr (by linarith)
  constructor <;> linarith

theorem force_trig_parameters (m : ℝ) (hm : 0 < m) (hmmax : m ≤ 29/20) :
    let v := forceAngle m/2
    0 < cos v ∧ cos v < 1 ∧ 0 < sin (v/2) ∧
    (cos v)^2=1-m/4 ∧ sqrt (1-m/4)=cos v ∧
    sqrt ((1-sqrt (1-m/4))/2)=sin (v/2) := by
  let v := forceAngle m/2
  have hv := force_v_range m hm hmmax
  have hx : 0 < cos v := Real.cos_pos_of_mem_Ioo ⟨by dsimp [v]; linarith [hv.1,Real.pi_pos],by dsimp [v]; linarith [hv.2,Real.pi_pos]⟩
  have hx1 : cos v < 1 := by
    have h := Real.strictAntiOn_cos (show (0:ℝ)∈Set.Icc 0 π by constructor <;> linarith [Real.pi_pos])
      (show v∈Set.Icc 0 π by dsimp [v]; constructor <;> linarith [hv.1,hv.2,Real.pi_pos]) hv.1
    simpa using h
  have hy : 0 < sin (v/2) := Real.sin_pos_of_pos_of_lt_pi (by dsimp [v]; linarith [hv.1])
    (by dsimp [v]; linarith [hv.2,Real.pi_pos])
  have hcos : cos (forceAngle m)=1-m/2 := Real.cos_arccos (by linarith) (by linarith)
  have hx2 : (cos v)^2=1-m/4 := by
    have he : 2*v=forceAngle m := by dsimp [v]; ring
    have h := Real.cos_two_mul v
    rw [he,hcos] at h
    linarith
  have hsx : sqrt (1-m/4)=cos v := by rw [← hx2,Real.sqrt_sq hx.le]
  have hsy : sqrt ((1-sqrt (1-m/4))/2)=sin (v/2) := by
    have h := Real.cos_two_mul' (v/2)
    rw [show 2*(v/2)=v by ring] at h
    have hsq : (1-cos v)/2=sin (v/2)^2 := by nlinarith [Real.sin_sq_add_cos_sq (v/2)]
    rw [hsx,hsq,Real.sqrt_sq hy.le]
  exact ⟨hx,hx1,hy,hx2,hsx,hsy⟩

theorem force_factor_bounds (m : ℝ) (hm : 0 < m) (hmmax : m ≤ 29/20) :
    1 < forceFactor m ∧ forceFactor m ≤ 2083/399 ∧ forceFactor m < 16/3 ∧ forceFactor m < 6 := by
  obtain ⟨hx,hx1,hy,hx2,hsx,hsy⟩ := force_trig_parameters m hm hmmax
  have hxlo : 399/500 ≤ cos (forceAngle m/2) := by nlinarith
  have hy2 : sin (forceAngle m/2/2)^2=(1-cos (forceAngle m/2))/2 := by
    have h := Real.cos_two_mul' (forceAngle m/2/2)
    rw [show 2*(forceAngle m/2/2)=forceAngle m/2 by ring] at h
    nlinarith [Real.sin_sq_add_cos_sq (forceAngle m/2/2)]
  have hyhi : sin (forceAngle m/2/2) ≤ 8/25 := by nlinarith
  have he : forceFactor m=(4+8*sin (forceAngle m/2/2))/cos (forceAngle m/2)-3 := by
    unfold forceFactor
    rw [hsy,hsx]
  have hl : 1 < forceFactor m := by
    rw [he]
    have hh : 4 < (4+8*sin (forceAngle m/2/2))/cos (forceAngle m/2) := (lt_div_iff₀ hx).mpr (by nlinarith)
    linarith
  have hu : forceFactor m ≤ 2083/399 := by
    rw [he]
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hx).mpr
    nlinarith
  exact ⟨hl,hu,by linarith,by linarith⟩

theorem force_factor_cot_identity (m : ℝ) (hm : 0 < m) (hmmax : m ≤ 29/20) :
    1+4*tan (forceAngle m/2)*(tan ((π-forceAngle m/2)/4))⁻¹=forceFactor m := by
  let v := forceAngle m/2
  have hv := force_v_range m hm hmmax
  obtain ⟨hx,hx1,hy,hx2,hsx,hsy⟩ := force_trig_parameters m hm hmmax
  have hw : 0 < cos (v/2) := Real.cos_pos_of_mem_Ioo ⟨by dsimp [v]; linarith [hv.1,Real.pi_pos],by dsimp [v]; linarith [hv.2,Real.pi_pos]⟩
  have hβ : 0 < π/2-v/2 ∧ π/2-v/2 < π := by dsimp [v]; constructor <;> linarith [hv.1,hv.2,Real.pi_pos]
  have hc := (positive_half_angle_products (π/2-v/2) hβ.1 hβ.2).2.2.2.2
  rw [Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub] at hc
  have hb : (π/2-v/2)/2=(π-v)/4 := by ring
  rw [hb] at hc
  have hsin : sin v=2*sin (v/2)*cos (v/2) := by
    simpa only [show 2*(v/2)=v by ring] using Real.sin_two_mul (v/2)
  have hysq : 2*sin (v/2)^2=1-cos v := by
    have h := Real.cos_two_mul' (v/2)
    rw [show 2*(v/2)=v by ring] at h
    nlinarith [Real.sin_sq_add_cos_sq (v/2)]
  change 1+4*tan v*(tan ((π-v)/4))⁻¹=forceFactor m
  unfold forceFactor
  rw [hsy,hsx]
  change 1+4*tan v*(tan ((π-v)/4))⁻¹=(4+8*sin (v/2))/cos v-3
  rw [Real.tan_eq_sin_div_cos,hsin]
  apply (eq_sub_iff_add_eq).mpr
  apply (eq_div_iff (show cos v ≠ 0 from hx.ne')).mpr
  field_simp [show cos v ≠ 0 from hx.ne']
  linear_combination 8*sin (v/2)*hc+4*hysq

#print axioms force_factor_bounds
#print axioms force_factor_cot_identity
end Blueprint.Thomson.Tail.Implementation
