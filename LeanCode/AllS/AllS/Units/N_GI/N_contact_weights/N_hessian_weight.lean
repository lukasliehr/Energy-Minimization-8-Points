import AllS.Units.N_GI.N_contact_weights.N_linear_lower

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem tail_exp_hessian_constant : exp ((63:ℝ)/50)<25/7 := by
  have h := Real.exp_bound (x := (63:ℝ)/100) (by norm_num) (n := 8) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  obtain ⟨_,hU⟩ := abs_le.mp h
  have hexp : exp ((63:ℝ)/100)<47/25 := by linarith
  have he : exp ((63:ℝ)/50)=(exp ((63:ℝ)/100))^2 := by
    rw [pow_two,←Real.exp_add]
    congr 1
    norm_num
  rw [he]
  nlinarith [Real.exp_pos ((63:ℝ)/100)]

theorem contact_weights_hessian_weight (p : ℝ) (hp : (97:ℝ)/2≤p) (q : TangentCoordinates)
    (hq : q∈convexTailDomain p) (e : ContactIndex) :
    (7:ℝ)/25<(tau/squaredDistance (orthographicChart q) e.1 (contactNext e))^(p+2) := by
  have hp0 : 0<p := by linarith
  have hq3 := tail_small_radius p hp q hq.2.1
  have hd : 0<squaredDistance (orthographicChart q) e.1 (contactNext e) := by
    have hsep := (balanced_energy_distinct_chart q hq3).2 _ _ (contactNext_ne e)
    unfold squaredDistance
    nlinarith
  have he := (abs_le.mp (contact_scaled_taylor_error p hp q hq.2.1 e)).2
  have hl := contact_weights_linear_upper p hp q hq e
  have hε := tail_epsilon_bounds p hp
  have hratio : 2/p≤2/((97:ℝ)/2) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp
  have hs : ((119:ℝ)/100+tailEpsilon p)*(1+2/p)<63/50 := by
    have h := mul_le_mul (show (119:ℝ)/100+tailEpsilon p≤119/100+621/50000 by linarith)
      (add_le_add (le_refl 1) hratio) (by positivity) (by norm_num)
    norm_num at h
    linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos hd tau_pos)
  have hδ : squaredDistance (orthographicChart q) e.1 (contactNext e)/tau-1=
      contactDelta q e.1 (contactNext e)/tau := by dsimp [contactDelta]; field_simp [tau_pos.ne'] <;> ring
  rw [hδ] at hlog
  have hlogmul := mul_le_mul_of_nonneg_left hlog (show 0≤p+2 by linarith)
  have hexponent : (p+2)*log (squaredDistance (orthographicChart q) e.1 (contactNext e)/tau)<63/50 := by
    have hx : (p/tau)*contactDelta q e.1 (contactNext e)<119/100+tailEpsilon p := by linarith
    have hmul := mul_lt_mul_of_pos_right hx (show 0<1+2/p by positivity)
    have hid : ((p/tau)*contactDelta q e.1 (contactNext e))*(1+2/p)=
        (p+2)*(contactDelta q e.1 (contactNext e)/tau) := by field_simp <;> ring
    rw [hid] at hmul
    exact hlogmul.trans_lt (hmul.trans hs)
  have hconst : (7:ℝ)/25<exp (-(63:ℝ)/50) := by
    rw [show -(63:ℝ)/50=-((63:ℝ)/50) by ring,Real.exp_neg]
    rw [←one_div]
    apply (lt_div_iff₀ (Real.exp_pos _)).mpr
    linarith [tail_exp_hessian_constant]
  apply hconst.trans
  rw [Real.rpow_def_of_pos (div_pos tau_pos hd)]
  apply Real.exp_lt_exp.mpr
  rw [Real.log_div tau_pos.ne' hd.ne']
  rw [Real.log_div hd.ne' tau_pos.ne'] at hexponent
  nlinarith

#print axioms contact_weights_hessian_weight
end Blueprint.Thomson.Tail.Implementation
