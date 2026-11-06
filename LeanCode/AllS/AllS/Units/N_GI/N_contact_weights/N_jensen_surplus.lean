import AllS.Units.N_GI.N_contact_weights.N_scalar_bounds

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def jensenU : ℝ := 3411/4000
def jensenW : ℝ := 1083/50
def jensenSurplus : ℝ := exp (-jensenU)-1+jensenU+jensenU^2/(2*(jensenW-1))

theorem exp_neg_surplus_mono (u x : ℝ) (hu : 0≤u) (hux : u≤x) :
    exp (-u)-1+u≤exp (-x)-1+x := by
  have he : exp (-u)≤1 := by simpa using Real.exp_le_exp.mpr (show -u≤0 by linarith)
  have ht := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (u-x)) (Real.exp_pos (-u)).le
  have heq : exp (-u)*exp (u-x)=exp (-x) := by rw [←Real.exp_add]; congr 1; ring
  rw [heq] at ht
  nlinarith [mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr hux)]

theorem jensen_surplus_lower (W w x : ℝ) (hw : 1≤w) (hwW : w<W)
    (hW : W≤jensenW) (hx : jensenU≤x) :
    W+jensenSurplus≤w*exp (-x)+(W-w)*exp (w*x/(W-w)) := by
  have hu : 0<jensenU := by norm_num [jensenU]
  have hwm : 0<W-w := sub_pos.mpr hwW
  have hx0 : 0<x := hu.trans_le hx
  have hwp : 0<w := by linarith
  have ht0 : 0≤w*x/(W-w) := by positivity
  have he2 := Real.sum_le_exp_of_nonneg ht0 3
  norm_num [Finset.sum_range_succ,Nat.factorial] at he2
  have hFu := Real.add_one_le_exp (-jensenU)
  have hmono := exp_neg_surplus_mono jensenU x hu.le hx
  have hF : exp (-jensenU)-1+jensenU≤w*(exp (-x)-1+x) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hw) (by linarith : 0≤exp (-x)-1+x)]
  have hwu : jensenU≤w*x := by nlinarith [mul_nonneg (sub_nonneg.mpr hw) hx0.le]
  have hsq : jensenU^2≤(w*x)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hwu) (by positivity : 0≤w*x+jensenU)]
  have hr : jensenU^2/(2*(jensenW-1))≤(w*x)^2/(2*(W-w)) := by
    calc
      _ ≤ jensenU^2/(2*(W-w)) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
      _ ≤ _ := div_le_div_of_nonneg_right hsq (by positivity)
  have he : (W-w)*(1+w*x/(W-w)+(w*x/(W-w))^2/2)=
      W-w+w*x+(w*x)^2/(2*(W-w)) := by field_simp <;> ring
  have hm := mul_le_mul_of_nonneg_left he2 hwm.le
  rw [he] at hm
  dsimp [jensenSurplus]
  nlinarith

theorem jensen_surplus_positive : 0<jensenSurplus := by
  have h := Real.add_one_le_exp (-jensenU)
  have hr : 0<jensenU^2/(2*(jensenW-1)) := by norm_num [jensenU,jensenW]
  dsimp [jensenSurplus]
  linarith

theorem jensen_common_strict :
    (3917:ℝ)/250<balancedLambda*(contactTotalWeight+jensenSurplus) := by
  have hl := tail_lambda_constants.2.1
  have hc := tail_Cmin_constants.1
  have he := Real.exp_bound (x := -(3411:ℝ)/4000) (by norm_num) (n := 10) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at he
  obtain ⟨heL,_⟩ := abs_le.mp he
  have hmul := mul_nonneg (sub_nonneg.mpr hl.le) jensen_surplus_positive.le
  dsimp [jensenSurplus,jensenU,jensenW] at hmul ⊢
  nlinarith

#print axioms jensen_surplus_lower
#print axioms jensen_common_strict
end Blueprint.Thomson.Tail.Implementation
