import AllS.Units.N_GI.N_cube_parameters.N_definitions

set_option maxHeartbeats 1200000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem cube_bounds_positive (c : ℝ) (hc : 0<c) : 0<cubeLower c ∧ 0<cubeUpper c := by
  unfold cubeLower cubeUpper
  constructor <;> positivity

theorem cube_bounds_reciprocal (c : ℝ) (hc : 0<c) :
    c^2/cubeUpper c=cubeLower c ∧ c^2/cubeLower c=cubeUpper c := by
  have hc0 := hc.ne'
  have hc1 : 1+c≠0 := by positivity
  unfold cubeUpper cubeLower
  constructor <;> field_simp <;> ring

theorem cube_dual_upper_iff (c q : ℝ) (hc : 0<c) (hq : 0<q) :
    c^2/q≤cubeUpper c ↔ cubeLower c≤q := by
  have hU := (cube_bounds_positive c hc).2
  have he := (cube_bounds_reciprocal c hc).1
  rw [←he,div_le_iff₀ hq,div_le_iff₀ hU]
  rw [mul_comm q]

theorem cube_dual_lower_iff (c q : ℝ) (hc : 0<c) (hq : 0<q) :
    cubeLower c≤c^2/q ↔ q≤cubeUpper c := by
  have hL := (cube_bounds_positive c hc).1
  have he := (cube_bounds_reciprocal c hc).2
  rw [←he,le_div_iff₀ hq,le_div_iff₀ hL]
  rw [mul_comm q]

theorem cube_dual_involution (c : ℝ) (q : Fin 3 → ℝ) (hc : 0<c) (hq : ∀k,0<q k) :
    cubeDual c (cubeDual c q)=q := by
  funext k
  unfold cubeDual
  field_simp [(hc.ne'),(hq k).ne']

theorem cube_dual_equations (c : ℝ) (q : Fin 3 → ℝ) (h : CubeEquations c q) :
    CubeEquations c (cubeDual c q) := by
  obtain ⟨hc,hq,hs,hr⟩ := h
  refine ⟨hc,fun k => div_pos (sq_pos_of_pos hc) (hq k),?_,?_⟩
  · simpa only [cubeDual,Finset.mul_sum,mul_one_div] using hr
  · calc
      c^2*(∑k,1/cubeDual c q k) = ∑k,q k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        unfold cubeDual
        field_simp [hc.ne',(hq k).ne']
      _ = 1 := hs

theorem cube_parameters_duality (c : ℝ) (q : Fin 3 → ℝ) (h : CubeFeasible c q) :
    CubeFeasible c (cubeDual c q) ∧ cubeDual c (cubeDual c q)=q ∧
    (∀k,cubeDual c q k=cubeUpper c ↔ q k=cubeLower c) ∧
    (∀k,cubeDual c q k=cubeLower c ↔ q k=cubeUpper c) := by
  have hc := h.1.1
  have hq := h.1.2.1
  have hb := cube_bounds_positive c hc
  refine ⟨⟨cube_dual_equations c q h.1,?_⟩,cube_dual_involution c q hc hq,?_,?_⟩
  · intro k
    exact ⟨(cube_dual_lower_iff c (q k) hc (hq k)).mpr (h.2 k).2,
      (cube_dual_upper_iff c (q k) hc (hq k)).mpr (h.2 k).1⟩
  · intro k
    unfold cubeDual
    rw [div_eq_iff (hq k).ne',←(cube_bounds_reciprocal c hc).1,eq_div_iff hb.2.ne']
    constructor <;> intro hh <;> nlinarith
  · intro k
    unfold cubeDual
    rw [div_eq_iff (hq k).ne',←(cube_bounds_reciprocal c hc).2,eq_div_iff hb.1.ne']
    constructor <;> intro hh <;> nlinarith

#print axioms cube_parameters_duality
end Blueprint.Thomson.Tail.Implementation
