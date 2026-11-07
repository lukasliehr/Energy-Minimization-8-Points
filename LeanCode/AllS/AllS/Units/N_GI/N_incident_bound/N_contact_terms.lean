import AllS.Units.N_GI.N_incident_bound.N_bi_upper

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem contact_normalized_term_upper (p : ℝ) (hp : (97:ℝ)/2≤p) (q : TangentCoordinates)
    (hq : q∈convexTailDomain p) (e : ContactIndex) :
    (tau/squaredDistance (orthographicChart q) e.1 (contactNext e))^(p+1) ≤
      (exp ((3:ℝ)/25)/(1-3/p))*exp (-contactScaledLinear p q e) := by
  have hp0 : 0<p := by linarith
  have hd : 0<squaredDistance (orthographicChart q) e.1 (contactNext e) := by
    have hsep := (balanced_energy_distinct_chart q (tail_small_radius p hp q hq.2.1)).2 _ _ (contactNext_ne e)
    unfold squaredDistance
    nlinarith
  have hratio : 0<tau/squaredDistance (orthographicChart q) e.1 (contactNext e) := div_pos tau_pos hd
  have hden : 0<1-3/p := by rw [sub_pos]; exact (div_lt_one hp0).mpr (by linarith)
  have hy := (abs_lt.mp (contact_weights_linear_lower p hp q hq e).2).1
  have hynorm : -3/p<contactDelta q e.1 (contactNext e)/tau := by
    apply (div_lt_iff₀ hp0).mpr
    simp only [div_eq_mul_inv] at hy ⊢
    nlinarith
  have he : squaredDistance (orthographicChart q) e.1 (contactNext e)/tau=
      1+contactDelta q e.1 (contactNext e)/tau := by
    dsimp [contactDelta]
    field_simp [tau_pos.ne']
    <;> ring
  have hbase : 1-3/p ≤ squaredDistance (orthographicChart q) e.1 (contactNext e)/tau := by
    rw [he]
    rw [neg_div] at hynorm
    linarith
  have hinv : tau/squaredDistance (orthographicChart q) e.1 (contactNext e)≤1/(1-3/p) := by
    have h := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤1) hden hbase
    simpa only [one_div,inv_div] using h
  have hlog := (abs_lt.mp (contact_weights_log_error p hp q hq e)).1
  have hpow : (tau/squaredDistance (orthographicChart q) e.1 (contactNext e))^p≤
      exp ((3:ℝ)/25)*exp (-contactScaledLinear p q e) := by
    rw [Real.rpow_def_of_pos hratio,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [Real.log_div tau_pos.ne' hd.ne']
    rw [Real.log_div hd.ne' tau_pos.ne'] at hlog
    nlinarith
  rw [Real.rpow_add hratio,Real.rpow_one]
  have h := mul_le_mul hpow hinv hratio.le (by positivity)
  convert! h using 1 <;> ring

theorem incident_contact_sum_upper (p : ℝ) (hp : (97:ℝ)/2≤p) (q : TangentCoordinates)
    (hq : q∈convexTailDomain p) (i : Fin 8) :
    (∑ e∈contactIncident i, (tau/squaredDistance (orthographicChart q) e.1 (contactNext e))^(p+1)) <
      ((51:ℝ)/10)*exp ((3:ℝ)/25)/(1-3/p) := by
  have hp0 : 0<p := by linarith
  have hden : 0<1-3/p := by rw [sub_pos]; exact (div_lt_one hp0).mpr (by linarith)
  have h := Finset.sum_le_sum (fun e (_ : e∈contactIncident i)=>contact_normalized_term_upper p hp q hq e)
  rw [←Finset.mul_sum] at h
  change _≤(exp ((3:ℝ)/25)/(1-3/p))*contactBi p q i at h
  have hb := mul_lt_mul_of_pos_left (incident_bound_bi_upper p hp q hq i) (div_pos (Real.exp_pos ((3:ℝ)/25)) hden)
  convert! h.trans_lt hb using 1 <;> ring

theorem incident_exp_upper : exp ((3:ℝ)/25)<113/100 := by
  have h := Real.exp_bound (x := (3:ℝ)/25) (by norm_num) (n := 5) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  obtain ⟨_,hU⟩ := abs_le.mp h
  linarith

theorem incident_total_scalar (p : ℝ) (hp : (97:ℝ)/2≤p) :
    ((51:ℝ)/10)*exp ((3:ℝ)/25)/(1-3/p)+1/1000<31/5 := by
  have hp0 : 0<p := by linarith
  have hquot : 3/p≤3/((97:ℝ)/2) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp
  have hden : 0<1-3/p := by linarith
  have hu := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left incident_exp_upper.le (by norm_num : (0:ℝ)≤51/10)) hden.le
  have hd := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤(51/10)*(113/100))
    (by norm_num : (0:ℝ)<1-3/(97/2)) (by linarith : 1-3/((97:ℝ)/2)≤1-3/p)
  have h := hu.trans hd
  norm_num at h
  linarith

#print axioms incident_contact_sum_upper
end Blueprint.Thomson.Tail.Implementation
