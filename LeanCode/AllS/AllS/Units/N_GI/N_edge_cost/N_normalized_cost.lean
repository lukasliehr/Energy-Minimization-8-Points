import AllS.Units.N_GI.N_edge_cost.N_two_geometric_bounds

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def normalizedEdgeCost (m : ℝ) (u : Point) (Y : Fin 8 → Point) (i j : Fin 8) : ℝ :=
  (sin (forceAngle m)/m)*(squaredDistance Y i j/orientedArea u Y i j)

theorem force_half_angle_ratios (m : ℝ) (hm : 0 < m) (hmm : m ≤ 29/20) :
    0 < tan (forceAngle m/2) ∧
    (sin (forceAngle m)/m)*2=(tan (forceAngle m/2))⁻¹ ∧
    (sin (forceAngle m)/m)*(2*m/(4-m))=tan (forceAngle m/2) := by
  have hc0 : (0:ℝ) < 1-m/2 := by linarith
  have hc1 : 1-m/2 < (1:ℝ) := by linarith
  have h0 : 0 < forceAngle m := Real.arccos_pos.mpr hc1
  have hp2 : forceAngle m < π/2 := Real.arccos_lt_pi_div_two.mpr hc0
  have hpi : forceAngle m < π := by linarith [Real.pi_pos]
  obtain ⟨ht,_,_,hleft,hright⟩ := positive_half_angle_products (forceAngle m) h0 hpi
  have hcos : cos (forceAngle m)=1-m/2 := Real.cos_arccos (by linarith) hc1.le
  rw [hcos] at hleft hright
  have hm4 : 4-m ≠ 0 := by linarith
  refine ⟨ht,?_,?_⟩
  · rw [inv_eq_one_div]
    apply (eq_div_iff ht.ne').mpr
    field_simp [hm.ne'] <;> nlinarith [hleft]
  · have htne := ht.ne'
    have he : sin (forceAngle m)=((4-m)/2)*tan (forceAngle m/2) := by
      have := congrArg (fun z : ℝ => z*tan (forceAngle m/2)) hright
      field_simp at this
      nlinarith
    rw [he]
    field_simp <;> ring

theorem reciprocal_bounds_one (c a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a*b=1) (hca : a ≤ c) (hcb : b ≤ c) : 1 ≤ c := by
  by_contra hc
  have hc1 : c < 1 := lt_of_not_ge hc
  have ha1 : a < 1 := hca.trans_lt hc1
  have hb1 : b < 1 := hcb.trans_lt hc1
  have hp : a*b < 1 := (mul_lt_mul_of_pos_right ha1 hb).trans (by simpa using hb1)
  linarith

theorem edge_cost_normalized_cost (Y : Fin 8 → Point) (p m : ℝ)
    (i₀ j₀ i j : Fin 8) (hY : IsConfiguration Y) (hp : 0 < p) (hstat : Stationary p Y)
    (hne : i₀ ≠ j₀) (hm : 0 < m) (hmmax : m ≤ 29/20)
    (hd : squaredDistance Y i₀ j₀=m) (hmin : ∀ i j, i ≠ j → m ≤ squaredDistance Y i j)
    (harea : 0 < orientedArea (forceAxis Y i₀ j₀ m) Y i j) :
    let u := forceAxis Y i₀ j₀ m
    let α := projectionAngle u (Y i) (Y j)
    let v := forceAngle m/2
    1 ≤ normalizedEdgeCost m u Y i j ∧
    max ((tan v)⁻¹*tan (α/2)) (tan v*(tan (α/2))⁻¹) ≤ normalizedEdgeCost m u Y i j ∧
    normalizedEdgeCost m u Y i₀ j₀=1 := by
  let u := forceAxis Y i₀ j₀ m
  let α := projectionAngle u (Y i) (Y j)
  let v := forceAngle m/2
  have haxis := forceAxis_spec Y hY m hm hmmax i₀ j₀ hd
  have hedge := edge_cost_projected_angle Y p m i₀ j₀ i j hY hp hstat hne hm hmmax hd hmin harea
  have hb := edge_cost_two_geometric_bounds Y p m i₀ j₀ i j hY hp hstat hne hm hmmax hd hmin harea
  obtain ⟨htv,hvleft,hvright⟩ := force_half_angle_ratios m hm hmmax
  have hta : 0 < tan (α/2) := Real.tan_pos_of_pos_of_lt_pi_div_two
    (by linarith [hedge.2.2.1]) (by linarith [hedge.2.2.2.1])
  have hs : 0 < sin (forceAngle m)/m := div_pos haxis.2.1 hm
  have hb1 : (tan v)⁻¹*tan (α/2) ≤ normalizedEdgeCost m u Y i j := by
    have h := mul_le_mul_of_nonneg_left hb.2.2.1 hs.le
    calc
      _ = (sin (forceAngle m)/m)*(2*tan (α/2)) := by rw [← hvleft]; ring
      _ ≤ _ := h
  have hb2 : tan v*(tan (α/2))⁻¹ ≤ normalizedEdgeCost m u Y i j := by
    have h := mul_le_mul_of_nonneg_left hb.2.2.2 hs.le
    calc
      _ = (sin (forceAngle m)/m)*((2*m/(4-m))*(tan (α/2))⁻¹) := by rw [← hvright]; ring
      _ ≤ _ := h
  refine ⟨reciprocal_bounds_one _ _ _ (mul_pos (inv_pos.mpr htv) hta)
    (mul_pos htv (inv_pos.mpr hta)) ?_ hb1 hb2,max_le hb1 hb2,?_⟩
  · field_simp [htv.ne',hta.ne']
  · change (sin (forceAngle m)/m)*(squaredDistance Y i₀ j₀/orientedArea u Y i₀ j₀)=1
    rw [hd,haxis.2.2.2]
    field_simp [hm.ne',haxis.2.1.ne']

#check edge_cost_normalized_cost
#print axioms edge_cost_normalized_cost
end Blueprint.Thomson.Tail.Implementation
