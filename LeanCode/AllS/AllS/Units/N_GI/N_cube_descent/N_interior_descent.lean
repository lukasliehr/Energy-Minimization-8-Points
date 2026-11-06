import AllS.Units.N_GI.N_cube_descent.N_value

noncomputable section
open Real Filter Topology
namespace Blueprint.Thomson.Tail.Implementation

def cubeSpread (q : Fin 3 → ℝ) (t : ℝ) : Fin 3 → ℝ := ![q 0-t,q 1+t,q 2]

@[simp] theorem cubeSpread_zero (q : Fin 3 → ℝ) : cubeSpread q 0=q := by
  ext k
  fin_cases k <;> simp [cubeSpread]

theorem cubeSpread_continuous (q : Fin 3 → ℝ) : Continuous (cubeSpread q) := by
  apply continuous_pi
  intro k
  fin_cases k <;> simp only [cubeSpread,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] <;> fun_prop

theorem cubeSpread_positive (q : Fin 3 → ℝ) (hq : ∀k,0<q k) (t : ℝ) (ht : 0<t) (ht0 : t<q 0) :
    ∀k,0<cubeSpread q t k := by
  intro k
  fin_cases k
  · change 0<q 0-t;linarith
  · change 0<q 1+t;linarith [hq 1]
  · exact hq 2

theorem cubeSpread_sum (q : Fin 3 → ℝ) (hs : ∑k,q k=1) (t : ℝ) : ∑k,cubeSpread q t k=1 := by
  rw [Fin.sum_univ_three] at hs ⊢
  change q 0-t+(q 1+t)+q 2=1
  linarith

theorem reciprocal_spread_strict (x y t : ℝ) (hx : 0<x) (hy : 0<y) (hxy : x<y)
    (ht : 0<t) (htx : t<x) : 1/x+1/y<1/(x-t)+1/(y+t) := by
  have hx' : 0<x-t := by linarith
  have hy' : 0<y+t := by linarith
  have hp : (x-t)*(y+t)<x*y := by nlinarith [mul_pos ht (show 0<y-x+t by linarith)]
  calc
    1/x+1/y=(x+y)/(x*y) := by field_simp;ring
    _<(x+y)/((x-t)*(y+t)) := div_lt_div_of_pos_left (by positivity) (mul_pos hx' hy') hp
    _=1/(x-t)+1/(y+t) := by field_simp;ring

theorem cubeSpread_reciprocal_strict (q : Fin 3 → ℝ) (hq : ∀k,0<q k) (h01 : q 0<q 1)
    (t : ℝ) (ht : 0<t) (ht0 : t<q 0) : (∑k,1/q k)<∑k,1/cubeSpread q t k := by
  have hh := reciprocal_spread_strict (q 0) (q 1) t (hq 0) (hq 1) h01 ht ht0
  simp only [Fin.sum_univ_three]
  change 1/q 0+1/q 1+1/q 2<1/(q 0-t)+1/(q 1+t)+1/q 2
  linarith

theorem cubeLower_continuousAt (c : ℝ) (hc : 0<c) : ContinuousAt cubeLower c := by
  unfold cubeLower
  fun_prop (disch := positivity)

theorem cubeUpper_continuous : Continuous cubeUpper := by unfold cubeUpper;fun_prop

theorem cube_interior_curve_ordered (c : ℝ) (q : Fin 3 → ℝ) (h : CubeFeasible c q)
    (hstrict : ∀k,cubeLower c<q k ∧ q k<cubeUpper c) (h01 : q 0<q 1) :
    CubeDescentCurve c q := by
  let Q : ℝ → Fin 3 → ℝ := cubeSpread q
  let C : ℝ → ℝ := fun t => cubeValue (Q t)
  have hQ : ContinuousAt Q 0 := (cubeSpread_continuous q).continuousAt
  have hQ0 : Q 0=q := cubeSpread_zero q
  have hC0 : C 0=c := by simp only [C,hQ0,cubeValue_eq c q h.1]
  have hC : ContinuousAt C 0 := by
    exact (hQ0 ▸ cubeValue_continuousAt q h.1.2.1).comp hQ
  have hb : ∀ᶠt in nhds (0:ℝ),∀k,cubeLower (C t)<Q t k ∧ Q t k<cubeUpper (C t) := by
    apply Filter.eventually_all.mpr
    intro k
    have hL := (cubeLower_continuousAt c h.1.1)
    have hU := cubeUpper_continuous.continuousAt (x := c)
    have hqk : ContinuousAt (fun t => Q t k) 0 := (continuousAt_pi.mp hQ) k
    exact ((hC0 ▸ hL).comp hC |>.eventually_lt hqk (by simpa only [Function.comp_apply,hC0,hQ0] using (hstrict k).1)).and
      (hqk.eventually_lt ((hC0 ▸ hU).comp hC) (by simpa only [Function.comp_apply,hC0,hQ0] using (hstrict k).2))
  refine ⟨fun t => (C t,Q t),hC.prodMk hQ,by change (C 0,Q 0)=(c,q);rw [hC0,hQ0],?_⟩
  have ht0 : ∀ᶠt in nhds (0:ℝ),t<q 0 := continuousAt_id.eventually_lt continuousAt_const (h.1.2.1 0)
  filter_upwards [nhdsWithin_le_nhds hb,nhdsWithin_le_nhds ht0,self_mem_nhdsWithin] with t hbt htq ht
  have htpos : 0<t := ht
  have hqt := cubeSpread_positive q h.1.2.1 t htpos htq
  refine ⟨⟨cubeValue_equations (Q t) hqt (cubeSpread_sum q h.1.2.2.1 t),fun k => ⟨(hbt k).1.le,(hbt k).2.le⟩⟩,?_⟩
  rw [←cubeValue_eq c q h.1]
  exact cubeValue_lt_of_sum q (Q t) h.1.2.1 hqt (cubeSpread_reciprocal_strict q h.1.2.1 h01 t htpos htq)

theorem cube_descent_interior_descent (c : ℝ) (q : Fin 3 → ℝ) (h : CubeFeasible c q)
    (hc : c<7/25) (hstrict : ∀k,cubeLower c<q k ∧ q k<cubeUpper c) :
    CubeDescentCurve c q ∧ HasCubeDescent c q := by
  obtain ⟨i,j,hij⟩ := cube_equations_unequal c q h.1 hc
  obtain ⟨e,he0,he1⟩ := fin3_equiv_pair i j (fun he => by rw [he] at hij;exact lt_irrefl _ hij)
  have hm := cube_interior_curve_ordered c (q ∘ e) (cube_feasible_reindex c q e h)
    (fun k => hstrict (e k)) (by simpa only [Function.comp_apply,he0,he1] using hij)
  have hh : CubeDescentCurve c q := by
    have hs := hm.reindex e.symm
    simpa only [Function.comp_def,Equiv.apply_symm_apply] using hs
  exact ⟨hh,hh.hasCubeDescent⟩

#print axioms cube_descent_interior_descent
end Blueprint.Thomson.Tail.Implementation
