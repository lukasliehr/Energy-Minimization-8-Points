import ThomsonNegative.Root
import ThomsonNegative.Auxiliary

noncomputable section
open Real
namespace ThomsonNegative

def seriesRoot (q a : ℝ) : ℝ :=
  16*auxSlope q ((1+a)/2)+16*auxSlope q a-
    8*(2+√2)*auxSlope q ((1-a)*(2+√2)/4)-
    8*(2-√2)*auxSlope q ((1-a)*(2-√2)/4)

lemma power_auxSlope (q d : ℝ) (hq : q ≠ 0) (hd : 0<d) :
    d^(-q) = (4:ℝ)^(-q)+q*(4:ℝ)^(-q)*auxSlope q (1-d/4) := by
  have hp : (4:ℝ)^(-q) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  unfold auxSlope
  rw [show 1-(1-d/4)=d/4 by ring,Real.div_rpow hd.le (by norm_num)]
  field_simp
  ring

/-- The polynomial-series root is exactly the showcase's stationarity equation,
up to a strictly positive factor. -/
theorem stationarity_series_bridge (q a : ℝ) (hq : q ≠ 0) (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    F (2*q-2) a = q*(4:ℝ)^(-q)*seriesRoot q a := by
  have hA : 1-dA a/4=(1+a)/2 := by unfold dA; ring
  have hB : 1-dB a/4=a := by unfold dB; ring
  have hC : 1-dC a/4=(1-a)*(2+√2)/4 := by unfold dC; ring
  have hD : 1-dD a/4=(1-a)*(2-√2)/4 := by unfold dD; ring
  dsimp only [F]
  rw [show 1+(2*q-2)/2=q by ring]
  rw [power_auxSlope q (dA a) hq (dA_pos ha.2),
      power_auxSlope q (dB a) hq (dB_pos ha.2),
      power_auxSlope q (dC a) hq (dC_pos ha.1.le),
      power_auxSlope q (dD a) hq (dD_pos ha.1.le),hA,hB,hC,hD]
  unfold seriesRoot
  ring

theorem stationarity_series_iff (q a : ℝ) (hq : 0<q) (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    F (2*q-2) a=0 ↔ seriesRoot q a=0 := by
  rw [stationarity_series_bridge q a hq.ne' ha]
  have hp : q*(4:ℝ)^(-q) ≠ 0 := mul_ne_zero hq.ne' (Real.rpow_pos_of_pos (by norm_num) _).ne'
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hp
  · intro h
    rw [h,mul_zero]

/-- One fixed rational height interval controls all four series arguments. -/
theorem contact_series_domain (a : ℝ) (ha : a ∈ Set.Icc (1/4:ℝ) (1/3)) :
    (1+a)/2 ∈ Set.Icc (0:ℝ) (2/3) ∧ a ∈ Set.Icc (0:ℝ) (2/3) ∧
    (1-a)*(2+√2)/4 ∈ Set.Icc (0:ℝ) (2/3) ∧
    (1-a)*(2-√2)/4 ∈ Set.Icc (0:ℝ) (2/3) := by
  have hr : 0 ≤ √(2:ℝ) := Real.sqrt_nonneg _
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hr3 : √(2:ℝ) ≤ 3/2 := by nlinarith
  have hprod := mul_le_mul (show 1-a ≤ (3/4:ℝ) by linarith [ha.1])
    (show 2+√(2:ℝ) ≤ 7/2 by linarith) (by positivity : (0:ℝ) ≤ 2+√2) (by norm_num : (0:ℝ) ≤ 3/4)
  have hprodD := mul_le_mul (show 1-a ≤ (3/4:ℝ) by linarith [ha.1])
    (show 2-√(2:ℝ) ≤ 2 by linarith) (by linarith : (0:ℝ) ≤ 2-√2) (by norm_num : (0:ℝ) ≤ 3/4)
  have hposC := mul_nonneg (show 0 ≤ 1-a by linarith [ha.2]) (show 0 ≤ 2+√(2:ℝ) by positivity)
  have hposD := mul_nonneg (show 0 ≤ 1-a by linarith [ha.2]) (show 0 ≤ 2-√(2:ℝ) by linarith)
  exact ⟨⟨by linarith [ha.1],by linarith [ha.2]⟩,
    ⟨by linarith [ha.1],by linarith [ha.2]⟩,
    ⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

#print axioms stationarity_series_bridge
#print axioms contact_series_domain
end ThomsonNegative
