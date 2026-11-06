import AllS.Units.N_FI.N_congruence.N_upper_frame

noncomputable section
open Real
namespace Blueprint.Thomson.Finite

theorem lower_axis_coordinate (a z : ℝ) (ha : a < 1)
    (hz : √(1-a)*z-a=contacts a 2 ∨ √(1-a)*z-a=contacts a 3) :
    z=√(1-a)/√2 ∨ z= -(√(1-a)/√2) := by
  have hr := Real.sqrt_pos.mpr (show 0 < 1-a by linarith)
  have hs := Real.sq_sqrt (show 0 ≤ 1-a by linarith)
  have he : √(1-a)*(√(1-a)/√2)=(1-a)/√2 := by rw [← mul_div_assoc,← pow_two,hs]
  rcases hz with hz | hz
  · left
    apply mul_left_cancel₀ hr.ne'
    change √(1-a)*z-a= -a+(1-a)/√2 at hz
    linarith
  · right
    apply mul_left_cancel₀ hr.ne'
    change √(1-a)*z-a= -a-(1-a)/√2 at hz
    rw [mul_neg]
    linarith

theorem upper_axis_dot (a : ℝ) (y : Point) :
    inner ℝ (X a 0) y=√(1-a)*y 0+√a*y 2 ∧
      inner ℝ (X a 1) y=√(1-a)*y 1+√a*y 2 := by
  constructor <;> rw [PiLp.inner_apply] <;>
    norm_num [X,Fin.sum_univ_succ] <;> ring

theorem congruence_lower_diagonals {a : ℝ} {Y : Fin 8 → Point} (ha : physical a)
    (S T : SquareRealization a Y) (hcent : T.center= -S.center)
    (hcross : ∀ i ∈ S.labels, ∀ j ∈ T.labels,
      inner ℝ (Y i) (Y j)=contacts a 2 ∨ inner ℝ (Y i) (Y j)=contacts a 3)
    (j : Fin 8) (hj : j ∈ T.labels) :
    let y := S.isometry.symm (Y j)
    y 2= -√a ∧ (y 0=√(1-a)/√2 ∨ y 0= -(√(1-a)/√2)) ∧
      (y 1=√(1-a)/√2 ∨ y 1= -(√(1-a)/√2)) := by
  let y := S.isometry.symm (Y j)
  have haI := physical_mem_Ioo a ha
  have hc := T.center_inner haI.1.le j hj
  rw [hcent,inner_neg_left] at hc
  have he : inner ℝ S.center (Y j)=√a*y 2 := by
    change inner ℝ (S.isometry (!₂[0,0,√a])) (Y j)=_
    calc
      _ = inner ℝ (S.isometry (!₂[0,0,√a])) (S.isometry y) := by dsimp [y]; rw [S.isometry.apply_symm_apply]
      _ = _ := by rw [S.isometry.inner_map_map,PiLp.inner_apply]; norm_num [Fin.sum_univ_succ]; ring
  have hy2 : y 2= -√a := by
    apply mul_left_cancel₀ (Real.sqrt_pos.mpr haI.1).ne'
    nlinarith [Real.sq_sqrt haI.1.le]
  have he2 : √a*y 2= -a := by linarith
  have haxes (k : Fin 4) : inner ℝ (Y (S.label k)) (Y j)=inner ℝ (X a (Fin.castAdd 4 k)) y := by
    rw [S.points]
    calc
      _ = inner ℝ (S.isometry (X a (Fin.castAdd 4 k))) (S.isometry y) := by dsimp [y]; rw [S.isometry.apply_symm_apply]
      _ = _ := S.isometry.inner_map_map _ _
  have hm (k : Fin 4) : S.label k ∈ S.labels := Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩
  have h0 := hcross _ (hm 0) j hj
  have h1 := hcross _ (hm 1) j hj
  rw [haxes 0] at h0
  rw [haxes 1] at h1
  change inner ℝ (X a 0) y=contacts a 2 ∨ inner ℝ (X a 0) y=contacts a 3 at h0
  change inner ℝ (X a 1) y=contacts a 2 ∨ inner ℝ (X a 1) y=contacts a 3 at h1
  rw [(upper_axis_dot a y).1,he2] at h0
  rw [(upper_axis_dot a y).2,he2] at h1
  exact ⟨hy2,lower_axis_coordinate a (y 0) haI.2 h0,lower_axis_coordinate a (y 1) haI.2 h1⟩

#check congruence_lower_diagonals
#print axioms congruence_lower_diagonals
end Blueprint.Thomson.Finite
