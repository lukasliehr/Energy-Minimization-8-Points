import AllS.Units.N_GI.N_cube_endgame.N_axis_reindex

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def antiprismCubeQ : Fin 3 → ℝ := ![cubeUpper packingHeight,cubeLower packingHeight,packingHeight]
def cubeU : ℝ := √(cubeUpper packingHeight)
def cubeL : ℝ := √(cubeLower packingHeight)
def cubeH : ℝ := √packingHeight
def cubeR : ℝ := √(1-packingHeight)

theorem antiprism_cube_bounds : cubeLower packingHeight+cubeUpper packingHeight=1-packingHeight ∧
    cubeLower packingHeight*cubeUpper packingHeight=packingHeight^2 := by
  have ha := packingHeight_mem_Ioo.1
  have hn : 1+packingHeight≠0 := by positivity
  constructor
  · unfold cubeLower cubeUpper
    field_simp [hn]
    nlinarith [packingHeight_quadratic]
  · unfold cubeLower cubeUpper
    field_simp [hn] <;> ring

theorem antiprism_cube_radicals :
    0<cubeU ∧ 0<cubeL ∧ 0<cubeH ∧ 0<cubeR ∧
    cubeU*cubeL=packingHeight ∧ cubeU^2+cubeL^2=cubeR^2 ∧
    (cubeU-cubeL)/√2=cubeL ∧ (cubeU+cubeL)/√2=cubeU ∧
    packingHeight/cubeU=cubeL ∧ packingHeight/cubeL=cubeU ∧ packingHeight/cubeH=cubeH := by
  have ha := packingHeight_mem_Ioo
  have hb := cube_bounds_positive packingHeight ha.1
  have hu : 0<cubeU := Real.sqrt_pos.mpr hb.2
  have hl : 0<cubeL := Real.sqrt_pos.mpr hb.1
  have hh : 0<cubeH := Real.sqrt_pos.mpr ha.1
  have hr : 0<cubeR := Real.sqrt_pos.mpr (by linarith [ha.2])
  have hu2 : cubeU^2=cubeUpper packingHeight := Real.sq_sqrt hb.2.le
  have hl2 : cubeL^2=cubeLower packingHeight := Real.sq_sqrt hb.1.le
  have hh2 : cubeH^2=packingHeight := Real.sq_sqrt ha.1.le
  have hr2 : cubeR^2=1-packingHeight := Real.sq_sqrt (by linarith [ha.2])
  have hprod : cubeU*cubeL=packingHeight := by
    have hs : (cubeU*cubeL)^2=packingHeight^2 := by
      rw [mul_pow,hu2,hl2,mul_comm,antiprism_cube_bounds.2]
    nlinarith [mul_pos hu hl]
  have hsum : cubeU^2+cubeL^2=cubeR^2 := by rw [hu2,hl2,hr2];linarith [antiprism_cube_bounds.1]
  have hdiff : cubeU^2-cubeL^2=2*packingHeight := by
    rw [hu2,hl2]
    have hb' := antiprism_cube_bounds.1
    unfold cubeUpper at hb' ⊢
    linarith
  have hs2 : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hspos : 0<√(2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hUL : cubeL<cubeU := by nlinarith
  have hm : cubeU-cubeL=√2*cubeL := by
    have he : (√2*cubeL)^2=2*cubeL^2 := by rw [mul_pow,hs2]
    nlinarith [mul_pos hspos hl]
  have hp : cubeU+cubeL=√2*cubeU := by
    have he : (√2*cubeU)^2=2*cubeU^2 := by rw [mul_pow,hs2]
    nlinarith [mul_pos hspos hu]
  refine ⟨hu,hl,hh,hr,hprod,hsum,?_,?_,?_,?_,?_⟩
  · apply (div_eq_iff hspos.ne').mpr;rw [hm];ring
  · apply (div_eq_iff hspos.ne').mpr;rw [hp];ring
  · apply (div_eq_iff hu.ne').mpr;nlinarith [hprod]
  · apply (div_eq_iff hl.ne').mpr;exact hprod.symm
  · apply (div_eq_iff hh.ne').mpr;nlinarith [hh2]

#print axioms antiprism_cube_radicals
end Blueprint.Thomson.Tail.Implementation
