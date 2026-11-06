import AllS.Units.N_G.N_cycle5

noncomputable section
open Real
open scoped BigOperators
namespace Blueprint.Thomson.Tail.Implementation

theorem force_triangle_bound (m : ℝ) (hm : 0 < m) (hmmax : m ≤ 29/20) :
    6 < 1+2*(tan (forceAngle m/2))⁻¹*tan ((π-forceAngle m/2)/2) := by
  let v := forceAngle m/2
  obtain ⟨hx,hx1,hy,hx2,_,_⟩ := force_trig_parameters m hm hmmax
  have hv := force_v_range m hm hmmax
  have hs : 0 < sin v := Real.sin_pos_of_pos_of_lt_pi hv.1 (by dsimp [v]; linarith [hv.2,Real.pi_pos])
  have hxlo : 5/7 < cos v := by change cos v^2=1-m/4 at hx2; nlinarith
  have hhalf := (positive_half_angle_products v hv.1 (by dsimp [v]; linarith [hv.2,Real.pi_pos])).2.2.2.2
  have hh : (tan (v/2))⁻¹=(1+cos v)/sin v := (eq_div_iff hs.ne').mpr hhalf
  have he : 1+2*(tan v)⁻¹*tan ((π-v)/2)=(1+cos v)/(1-cos v) := by
    rw [show (π-v)/2=π/2-v/2 by ring,Real.tan_pi_div_two_sub,hh,Real.tan_eq_sin_div_cos,inv_div]
    apply (eq_div_iff (show 1-cos v ≠ 0 by exact ne_of_gt (by linarith))).mpr
    field_simp [hs.ne']
    have hsq := Real.sin_sq_add_cos_sq v
    linear_combination -2*cos v*hsq
  change 6 < 1+2*(tan v)⁻¹*tan ((π-v)/2)
  rw [he]
  apply (lt_div_iff₀ (show 0 < 1-cos v by linarith)).mpr
  linarith

theorem cycle34_triangle (Y : Fin 8 → Point) (p m : ℝ) (i₀ j₀ : Fin 8)
    (hY : IsConfiguration Y) (hp : 0 < p) (hstat : Stationary p Y) (hne : i₀ ≠ j₀)
    (hm : 0 < m) (hmmax : m ≤ 29/20) (hd : squaredDistance Y i₀ j₀=m)
    (hmin : ∀ i j, i ≠ j → m ≤ squaredDistance Y i j)
    (C : FlowCycle) (hC : C.Positive (forceFlow p (forceAxis Y i₀ j₀ m) Y))
    (hlen : C.size+1=3) (hcontains : ∃ k₀, C.point k₀=i₀ ∧ C.point (k₀+1)=j₀) :
    forceFactor m < 6 ∧ 6 < cycleNormalizedCost m Y (forceAxis Y i₀ j₀ m) C := by
  obtain ⟨k₀,hk₀,hk₁⟩ := hcontains
  obtain ⟨q,_,hsum,_,hcases,_,_⟩ := cycle_winding Y p m i₀ j₀ hY hm hmmax hd C hC
  have hq := hcases (Or.inl hlen)
  subst q
  have hj := (positive_cycle_jensen Y p m i₀ j₀ hY hp hstat hne hm hmmax hd hmin C hC k₀ hk₀ hk₁ 1 hsum).1
  have hn : C.size=2 := by omega
  simp only [hn,Nat.cast_ofNat,Int.cast_one,mul_one] at hj
  exact ⟨(force_factor_bounds m hm hmmax).2.2.2,by nlinarith [force_triangle_bound m hm hmmax]⟩

#check cycle34_triangle
#print axioms cycle34_triangle
end Blueprint.Thomson.Tail.Implementation
