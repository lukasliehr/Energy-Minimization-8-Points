import Coulomb8.RootSigns
import Mathlib.Topology.Order.IntermediateValue

namespace Coulomb8

theorem q_pos : 0 < q := Real.sqrt_pos.mpr (by norm_num)
theorem q_sq : q^2=2 := Real.sq_sqrt (by norm_num)
theorem q_lt_two : q < 2 := by nlinarith [q_sq,q_pos]

theorem dMinus_pos {s : ℝ} (hs : 0 < s) : 0 < dMinus s := by
  have h := mul_pos (show 0 < 2+q by linarith [q_pos]) hs
  unfold dMinus
  linarith [q_lt_two]

theorem dPlus_pos {s : ℝ} (hs : 0 < s) : 0 < dPlus s := by
  have h := mul_pos (show 0 < 2-q by linarith [q_lt_two]) hs
  unfold dPlus
  linarith [q_pos]

theorem div_sqrt_strictAnti {c x y : ℝ} (hc : 0 < c) (hx : 0 < x) (hxy : x < y) :
    c/(y*Real.sqrt y) < c/(x*Real.sqrt x) := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hprod : x*Real.sqrt x < y*Real.sqrt y :=
    (mul_lt_mul_of_pos_right hxy hs).trans_le
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hxy.le) (hx.trans hxy).le)
  exact div_lt_div_of_pos_left hc (mul_pos hx hs) hprod

theorem F_strictMono : StrictMonoOn F (Set.Ioo 0 1) := by
  intro s hs t ht hst
  have hfirst := div_sqrt_strictAnti
    (show 0 < 2*q+1 by linarith [q_pos])
    (show 0 < 1-t by linarith [ht.2]) (show 1-t < 1-s by linarith)
  have hdm : dMinus s < dMinus t := by
    have h := mul_pos (show 0 < 2+q by linarith [q_pos]) (sub_pos.mpr hst)
    dsimp only [dMinus]
    nlinarith
  have hdp : dPlus s < dPlus t := by
    have h := mul_pos (show 0 < 2-q by linarith [q_lt_two]) (sub_pos.mpr hst)
    dsimp only [dPlus]
    nlinarith
  have hm := div_sqrt_strictAnti
    (show 0 < 4*(2+q) by nlinarith [q_pos]) (dMinus_pos hs.1) hdm
  have hp := div_sqrt_strictAnti
    (show 0 < 4*(2-q) by nlinarith [q_lt_two]) (dPlus_pos hs.1) hdp
  unfold F
  linarith

theorem F_continuousOn : ContinuousOn F (Set.Ioo 0 1) := by
  intro s hs
  have h1 : 0 < 1-s := by linarith [hs.2]
  have hm := dMinus_pos hs.1
  have hp := dPlus_pos hs.1
  dsimp only [dMinus,dPlus] at hm hp
  apply ContinuousAt.continuousWithinAt
  unfold F dMinus dPlus
  fun_prop (disch := positivity)

theorem endpoints_order : (0 : ℝ) < leftEndpoint ∧
    (leftEndpoint : ℝ) < rightEndpoint ∧ (rightEndpoint : ℝ) < 1/3 := by
  norm_num [leftEndpoint,rightEndpoint]

theorem exists_root : ∃ s : ℝ, s ∈ Set.Icc (leftEndpoint : ℝ) rightEndpoint ∧ F s=0 := by
  have hsubset : Set.Icc (leftEndpoint : ℝ) rightEndpoint ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro s hs
    constructor <;> linarith [endpoints_order.1,endpoints_order.2.2,hs.1,hs.2]
  have h := intermediate_value_Icc endpoints_order.2.1.le (F_continuousOn.mono hsubset)
  exact h ⟨F_left_negative.le,F_right_positive.le⟩

noncomputable def a : ℝ := Classical.choose exists_root

theorem a_bracket : a ∈ Set.Icc (leftEndpoint : ℝ) rightEndpoint :=
  (Classical.choose_spec exists_root).1
theorem F_a : F a=0 := (Classical.choose_spec exists_root).2
theorem a_pos : 0 < a := endpoints_order.1.trans_le a_bracket.1
theorem a_lt_third : a < 1/3 := a_bracket.2.trans_lt endpoints_order.2.2
theorem a_lt_one : a < 1 := by linarith [a_lt_third]

theorem root_unique {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hf : F s=0) : s=a :=
  F_strictMono.injOn hs ⟨a_pos,a_lt_one⟩ (hf.trans F_a.symm)

end Coulomb8

#print axioms Coulomb8.F_a
#print axioms Coulomb8.root_unique
