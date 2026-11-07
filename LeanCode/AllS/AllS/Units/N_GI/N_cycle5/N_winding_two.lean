import AllS.Units.N_GI.N_cycle5.N_winding_one

noncomputable section
open Real
open scoped BigOperators
namespace Blueprint.Thomson.Tail.Implementation

theorem force_cot_lower (m : ℝ) (hm : 0 < m) (hmmax : m ≤ 29/20) :
    5/4 < (tan (forceAngle m/2))⁻¹ := by
  let v := forceAngle m/2
  obtain ⟨hx,hx1,hy,hx2,_,_⟩ := force_trig_parameters m hm hmmax
  have hv := force_v_range m hm hmmax
  have hs : 0 < sin v := Real.sin_pos_of_pos_of_lt_pi hv.1 (by dsimp [v]; linarith [hv.2,Real.pi_pos])
  change 5/4 < (tan v)⁻¹
  rw [Real.tan_eq_sin_div_cos,inv_div]
  apply (lt_div_iff₀ hs).mpr
  by_contra hh
  have hb := mul_self_le_mul_self hx.le (le_of_not_gt hh)
  have ht := Real.sin_sq_add_cos_sq v
  change cos v^2=1-m/4 at hx2
  nlinarith

theorem cycle5_winding_two (Y : Fin 8 → Point) (p m : ℝ) (i₀ j₀ : Fin 8)
    (hY : IsConfiguration Y) (hp : 0 < p) (hstat : Stationary p Y) (hne : i₀ ≠ j₀)
    (hm : 0 < m) (hmmax : m ≤ 29/20) (hd : squaredDistance Y i₀ j₀=m)
    (hmin : ∀ i j, i ≠ j → m ≤ squaredDistance Y i j)
    (C : FlowCycle) (hC : C.Positive (forceFlow p (forceAxis Y i₀ j₀ m) Y))
    (hlen : C.size+1=5) (k₀ : Fin (C.size+1)) (hk₀ : C.point k₀=i₀) (hk₁ : C.point (k₀+1)=j₀)
    (hsum : ∑ i,cycleProjectedAngle Y (forceAxis Y i₀ j₀ m) C i=2*π*2) :
    let v := forceAngle m/2
    forceFactor m < 6 ∧ 6 < 1+4*(tan v)⁻¹ ∧
      1+4*(tan v)⁻¹ < cycleNormalizedCost m Y (forceAxis Y i₀ j₀ m) C := by
  let v := forceAngle m/2
  have hv := force_v_range m hm hmmax
  have hj := (positive_cycle_jensen Y p m i₀ j₀ hY hp hstat hne hm hmmax hd hmin C hC
    k₀ hk₀ hk₁ 2 (by simpa using hsum)).1
  have hn : C.size=4 := by omega
  simp only [hn,Nat.cast_ofNat,Int.cast_ofNat] at hj
  have ht : 1 < tan ((π*2-v)/4) := by
    have h := Real.strictMonoOn_tan
      (show π/4 ∈ Set.Ioo (-(π/2)) (π/2) by constructor <;> linarith [Real.pi_pos])
      (show (π*2-v)/4 ∈ Set.Ioo (-(π/2)) (π/2) by dsimp [v]; constructor <;> linarith [Real.pi_pos,hv.1,hv.2])
      (show π/4 < (π*2-v)/4 by dsimp [v]; linarith [Real.pi_pos,hv.2])
    simpa using h
  have hc : 5/4 < (tan v)⁻¹ := force_cot_lower m hm hmmax
  refine ⟨(force_factor_bounds m hm hmmax).2.2.2,by linarith,?_⟩
  change 1+4*(tan v)⁻¹ < _
  change 1+(tan v)⁻¹*4*tan ((π*2-v)/4) ≤ _ at hj
  nlinarith

#check cycle5_winding_two
#print axioms cycle5_winding_two
end Blueprint.Thomson.Tail.Implementation
