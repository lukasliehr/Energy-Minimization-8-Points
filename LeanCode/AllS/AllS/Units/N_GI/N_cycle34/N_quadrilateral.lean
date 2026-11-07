import AllS.Units.N_GI.N_cycle34.N_quad_polynomial

noncomputable section
open Real
open scoped BigOperators
namespace Blueprint.Thomson.Tail.Implementation

theorem force_quad_bound (m : ℝ) (hm : 0 < m) (hmmax : m ≤ 29/20) :
    16/3 ≤ 1+3*(tan (forceAngle m/2))⁻¹*tan ((π-forceAngle m/2)/3) := by
  let v := forceAngle m/2
  let b := tan ((π-v)/3)
  let q := b^2
  have hv := force_v_range m hm hmmax
  obtain ⟨_,_,hrel⟩ := force_quad_triple v hv.1 hv.2
  obtain ⟨hq1,hq3,hq6⟩ := cycle34_quad_polynomial m hm hmmax
  have hd : 0 < 3-q := by dsimp [q,b,v]; linarith
  have he : 1+3*(tan v)⁻¹*b=8*q/(3-q) := by
    apply (eq_div_iff hd.ne').mpr
    dsimp [q,b]
    linear_combination 3*hrel
  change 16/3 ≤ 1+3*(tan v)⁻¹*b
  rw [he]
  apply (le_div_iff₀ hd).mpr
  change 6/5 ≤ q at hq6
  linarith

theorem cycle34_quadrilateral (Y : Fin 8 → Point) (p m : ℝ) (i₀ j₀ : Fin 8)
    (hY : IsConfiguration Y) (hp : 0 < p) (hstat : Stationary p Y) (hne : i₀ ≠ j₀)
    (hm : 0 < m) (hmmax : m ≤ 29/20) (hd : squaredDistance Y i₀ j₀=m)
    (hmin : ∀ i j, i ≠ j → m ≤ squaredDistance Y i j)
    (C : FlowCycle) (hC : C.Positive (forceFlow p (forceAxis Y i₀ j₀ m) Y))
    (hlen : C.size+1=4) (hcontains : ∃ k₀, C.point k₀=i₀ ∧ C.point (k₀+1)=j₀) :
    forceFactor m < 16/3 ∧ 16/3 ≤ cycleNormalizedCost m Y (forceAxis Y i₀ j₀ m) C := by
  obtain ⟨k₀,hk₀,hk₁⟩ := hcontains
  obtain ⟨q,_,hsum,_,hcases,_,_⟩ := cycle_winding Y p m i₀ j₀ hY hm hmmax hd C hC
  have hq := hcases (Or.inr hlen)
  subst q
  have hj := (positive_cycle_jensen Y p m i₀ j₀ hY hp hstat hne hm hmmax hd hmin C hC k₀ hk₀ hk₁ 1 hsum).1
  have hn : C.size=3 := by omega
  simp only [hn,Nat.cast_ofNat,Int.cast_one,mul_one] at hj
  exact ⟨(force_factor_bounds m hm hmmax).2.2.1,by nlinarith [force_quad_bound m hm hmmax]⟩

#check cycle34_quadrilateral
#print axioms cycle34_quadrilateral
end Blueprint.Thomson.Tail.Implementation
