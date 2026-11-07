import Blueprint.FiniteDefinitions

noncomputable section
open Real
namespace Blueprint.Thomson.Finite

private theorem negative_power_ratio (u v p : ℝ) (hu : 0 < u) (hv : 0 < v) :
    v ^ (-p) = u ^ (-p) * (u/v)^p := by
  rw [Real.div_rpow hu.le hv.le, Real.rpow_neg hu.le, Real.rpow_neg hv.le]
  have hn : u ^ p ≠ 0 := (Real.rpow_pos_of_pos hu p).ne'
  field_simp

theorem height_upper_third_positive (s : ℝ) (hs : 0 ≤ s) : 0 < F s (1/3) := by
  let p : ℝ := 1+s/2
  let x : ℝ := (4+√2)/7
  let y : ℝ := (4-√2)/7
  let α : ℝ := (2+√2)/2
  let β : ℝ := (2-√2)/2
  have hr := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hr0 := Real.sqrt_nonneg (2 : ℝ)
  have hr1 : (1 : ℝ) < √2 := by nlinarith
  have hr2 : √(2 : ℝ) < 3/2 := by nlinarith
  have hp : 1 ≤ p := by dsimp [p]; linarith
  have hx0 : (1/2 : ℝ) < x := by dsimp [x]; linarith
  have hx1 : x < 1 := by dsimp [x]; linarith
  have hy0 : 0 < y := by dsimp [y]; linarith
  have hy1 : y < (1/2 : ℝ) := by dsimp [y]; linarith
  have hα : 0 < α := by dsimp [α]; positivity
  have hβ : 0 < β := by dsimp [β]; linarith
  have hsum : α+β=2 := by dsimp [α,β]; ring
  have hK : α*(2*x-1) < 1 := by dsimp [α,x]; nlinarith
  have hchord := (convexOn_rpow hp).2
    (show (1 : ℝ) ∈ Set.Ici 0 by norm_num)
    (show (1/2 : ℝ) ∈ Set.Ici 0 by norm_num)
    (show 0 ≤ 2*x-1 by linarith)
    (show 0 ≤ 2-2*x by linarith)
    (show (2*x-1)+(2-2*x)=1 by ring)
  simp only [smul_eq_mul, Real.one_rpow, mul_one] at hchord
  rw [show 2*x-1+(2-2*x)*(1/2)=x by ring] at hchord
  have hybound := Real.rpow_le_rpow hy0.le hy1.le (by linarith : 0 ≤ p)
  have hhalf := Real.rpow_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) < 1) (by linarith : 0 < p)
  have hprod := mul_pos (sub_pos.mpr hK) (sub_pos.mpr hhalf)
  have hαbound := mul_le_mul_of_nonneg_left hchord hα.le
  have hβbound := mul_le_mul_of_nonneg_left hybound hβ.le
  have hE : 0 < 1+(1/2 : ℝ)^p-α*x^p-β*y^p := by
    calc
      0 < (1-α*(2*x-1))*(1-(1/2 : ℝ)^p) := hprod
      _ = 1+(1/2 : ℝ)^p-α*((2*x-1)+(2-2*x)*(1/2 : ℝ)^p)-β*(1/2 : ℝ)^p := by
        have hβeq : β=2-α := by linarith
        rw [hβeq]
        ring
      _ ≤ _ := by linarith only [hαbound,hβbound]
  have hA : 0 < dA (1/3) := by norm_num [dA]
  have hB : 0 < dB (1/3) := by norm_num [dB]
  have hC : 0 < dC (1/3) := by dsimp [dC]; nlinarith
  have hD : 0 < dD (1/3) := by dsimp [dD]; nlinarith
  have hAB : dA (1/3)/dB (1/3) = (1/2 : ℝ) := by norm_num [dA,dB]
  have hAC : dA (1/3)/dC (1/3) = x := by
    apply (div_eq_iff hC.ne').2
    dsimp [dA,dC,x]
    nlinarith
  have hAD : dA (1/3)/dD (1/3) = y := by
    apply (div_eq_iff hD.ne').2
    dsimp [dA,dD,y]
    nlinarith
  have hBp := negative_power_ratio _ _ p hA hB
  have hCp := negative_power_ratio _ _ p hA hC
  have hDp := negative_power_ratio _ _ p hA hD
  rw [hAB] at hBp
  rw [hAC] at hCp
  rw [hAD] at hDp
  have hfact : F s (1/3) = 16*dA (1/3)^(-p) *
      (1+(1/2 : ℝ)^p-α*x^p-β*y^p) := by
    change 16*dA (1/3)^(-p)+16*dB (1/3)^(-p)-
      8*(2+√2)*dC (1/3)^(-p)-8*(2-√2)*dD (1/3)^(-p)=_
    rw [hBp,hCp,hDp]
    dsimp [α,β]
    ring
  rw [hfact]
  exact mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos hA _)) hE

#check height_upper_third_positive
#print axioms height_upper_third_positive
end Blueprint.Thomson.Finite
