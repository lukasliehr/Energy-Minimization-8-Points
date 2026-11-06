import AllS.Units.N_GI.N_edge_cost.N_projected_angle

noncomputable section
open Real
open SquareAntiprismVerification (crossVec)
namespace Blueprint.Thomson.Tail.Implementation

theorem positive_half_angle_products (α : ℝ) (h0 : 0 < α) (hπ : α < π) :
    0 < tan (α/2) ∧ 0 < 1-cos α ∧ 0 < 1+cos α ∧
    tan (α/2)*sin α=1-cos α ∧ (tan (α/2))⁻¹*sin α=1+cos α := by
  have hs : 0 < sin (α/2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hc : 0 < cos (α/2) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],by linarith⟩
  have hsin : sin α=2*sin (α/2)*cos (α/2) := by
    simpa only [show 2*(α/2)=α by ring] using Real.sin_two_mul (α/2)
  have hcos : cos α=2*cos (α/2)^2-1 := by
    simpa only [show 2*(α/2)=α by ring] using Real.cos_two_mul (α/2)
  have hid := Real.sin_sq_add_cos_sq (α/2)
  refine ⟨Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith),?_,?_,?_,?_⟩
  · nlinarith [sq_pos_of_pos hs]
  · nlinarith [sq_pos_of_pos hc]
  · rw [Real.tan_eq_sin_div_cos,hsin,hcos]
    field_simp
    nlinarith
  · rw [Real.tan_eq_sin_div_cos,inv_div,hsin,hcos]
    field_simp
    ring

theorem projection_two_cs (u x y : Point) (hu : ‖u‖=1) (hx : ‖x‖=1) (hy : ‖y‖=1) :
    projectionRadius u x*projectionRadius u y+projectionHeight u x*projectionHeight u y ≤ 1 ∧
    projectionRadius u x*projectionRadius u y-projectionHeight u x*projectionHeight u y ≤ 1 := by
  have h1 := projectionRadius_sq u x hu hx
  have h2 := projectionRadius_sq u y hu hy
  constructor
  · nlinarith [sq_nonneg (projectionRadius u x-projectionRadius u y),
      sq_nonneg (projectionHeight u x-projectionHeight u y)]
  · nlinarith [sq_nonneg (projectionRadius u x-projectionRadius u y),
      sq_nonneg (projectionHeight u x+projectionHeight u y)]

theorem projection_geometry_bounds (u x y : Point) (hu : ‖u‖=1) (hx : ‖x‖=1) (hy : ‖y‖=1)
    (m : ℝ) (hm : 0 < m) (hmin : m ≤ 2-2*inner ℝ x y)
    (harea : 0 < inner ℝ u (crossVec x y)) :
    let d := 2-2*inner ℝ x y
    let α := projectionAngle u x y
    0 < d ∧ d < 4 ∧
    2*tan (α/2) ≤ d/inner ℝ u (crossVec x y) ∧
    (2*m/(4-m))*(tan (α/2))⁻¹ ≤ d/inner ℝ u (crossVec x y) := by
  let d := 2-2*inner ℝ x y
  let α := projectionAngle u x y
  let r := projectionRadius u x*projectionRadius u y
  let δ := inner ℝ u (crossVec x y)
  obtain ⟨hrx,hry,ha0,hapi,ha,hinner⟩ := projected_angle_spec u x y hu hx hy harea
  obtain ⟨htan,hcosminus,hcosplus,hts,hits⟩ := positive_half_angle_products α ha0 hapi
  obtain ⟨hcsplus,hcsminus⟩ := projection_two_cs u x y hu hx hy
  have hr : 0 < r := mul_pos hrx hry
  have hd : 0 < d := hm.trans_le hmin
  have hlower : 2*r*(1-cos α) ≤ d := by dsimp [d,r,α]; nlinarith [hinner]
  have hupper : 2*r*(1+cos α) ≤ 4-d := by dsimp [d,r,α]; nlinarith [hinner]
  have hd4 : d < 4 := by
    have hp : 0 < 2*r*(1+cos α) := mul_pos (mul_pos (by norm_num) hr) hcosplus
    linarith
  have hdm : 0 < 4-d := by linarith
  have hmm : 0 < 4-m := by linarith
  have hb1 : 2*tan (α/2) ≤ d/δ := by
    apply (le_div_iff₀ harea).mpr
    change 2*tan (α/2)*(inner ℝ u (crossVec x y)) ≤ d
    rw [ha]
    calc
      _ = 2*r*(tan (α/2)*sin α) := by dsimp [r,α]; ring
      _ ≤ d := by rw [hts]; exact hlower
  have hb2 : (2*d/(4-d))*(tan (α/2))⁻¹ ≤ d/δ := by
    apply (le_div_iff₀ harea).mpr
    change (2*d/(4-d))*(tan (α/2))⁻¹*(inner ℝ u (crossVec x y)) ≤ d
    rw [ha]
    calc
      _ = (d/(4-d))*(2*r*((tan (α/2))⁻¹*sin α)) := by dsimp [r,α]; ring
      _ = (d/(4-d))*(2*r*(1+cos α)) := by rw [hits]
      _ ≤ (d/(4-d))*(4-d) := mul_le_mul_of_nonneg_left hupper (div_nonneg hd.le hdm.le)
      _ = d := div_mul_cancel₀ _ hdm.ne'
  have hfrac : 2*m/(4-m) ≤ 2*d/(4-d) := by
    apply (div_le_div_iff₀ hmm hdm).mpr
    nlinarith
  exact ⟨hd,hd4,hb1,(mul_le_mul_of_nonneg_right hfrac (inv_nonneg.mpr htan.le)).trans hb2⟩

theorem edge_cost_two_geometric_bounds (Y : Fin 8 → Point) (p m : ℝ)
    (i₀ j₀ i j : Fin 8) (hY : IsConfiguration Y) (_hp : 0 < p) (_hstat : Stationary p Y)
    (_hne : i₀ ≠ j₀) (hm : 0 < m) (hmmax : m ≤ 29/20)
    (hd : squaredDistance Y i₀ j₀=m) (hmin : ∀ i j, i ≠ j → m ≤ squaredDistance Y i j)
    (harea : 0 < orientedArea (forceAxis Y i₀ j₀ m) Y i j) :
    let u := forceAxis Y i₀ j₀ m
    let α := projectionAngle u (Y i) (Y j)
    0 < squaredDistance Y i j ∧ squaredDistance Y i j < 4 ∧
    2*tan (α/2) ≤ squaredDistance Y i j/orientedArea u Y i j ∧
    (2*m/(4-m))*(tan (α/2))⁻¹ ≤ squaredDistance Y i j/orientedArea u Y i j := by
  have hij : i ≠ j := by
    intro he
    subst j
    simpa [orientedArea_self] using harea
  have h := projection_geometry_bounds (forceAxis Y i₀ j₀ m) (Y i) (Y j)
    (forceAxis_spec Y hY m hm hmmax i₀ j₀ hd).2.2.1 (hY.1 i) (hY.1 j) m hm
    (by simpa [squaredDistance_inner Y hY] using hmin i j hij) harea
  simpa [squaredDistance_inner Y hY,orientedArea] using h

#check edge_cost_two_geometric_bounds
#print axioms edge_cost_two_geometric_bounds
end Blueprint.Thomson.Tail.Implementation
