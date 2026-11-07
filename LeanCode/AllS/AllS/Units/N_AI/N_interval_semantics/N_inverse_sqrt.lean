import AllS.Units.N_AI.N_interval_semantics.N_product
import Blueprint.Target

namespace Blueprint.CAP
def IntervalInverseSqrtStatement : Prop :=
  (∀ {I K : Box} {x : ℝ}, I.WellFormed → K.WellFormed → I.Contains x →
    Box.InvGate I K → K.Contains (1/x) ∧ x≠0) ∧
  (∀ {I K : Box} {x : ℝ}, I.WellFormed → K.WellFormed → I.Contains x →
    Box.SqrtGate I K → K.Contains (Real.sqrt x))
theorem Box.contains_inverse {I K : Box} {x : ℝ}
    (hx : I.Contains x) (hg : I.InvGate K) : K.Contains (1/x) ∧ x≠0 := by
  have hl : (K.lo:ℝ) ≤ 1/(I.hi:ℝ) := by exact_mod_cast hg.2.1
  have hu : 1/(I.lo:ℝ) ≤ (K.hi:ℝ) := by exact_mod_cast hg.2.2
  rcases hg.1 with hp | hn
  · have hpR : (0:ℝ)<I.lo := by exact_mod_cast hp
    have hxp : 0<x := hpR.trans_le hx.1
    exact ⟨⟨hl.trans (one_div_le_one_div_of_le hxp hx.2),
      (one_div_le_one_div_of_le hpR hx.1).trans hu⟩, ne_of_gt hxp⟩
  · have hnR : (I.hi:ℝ)<0 := by exact_mod_cast hn
    have hxn : x<0 := hx.2.trans_lt hnR
    exact ⟨⟨hl.trans (one_div_le_one_div_of_neg_of_le hnR hx.2),
      (one_div_le_one_div_of_neg_of_le hxn hx.1).trans hu⟩, ne_of_lt hxn⟩

theorem Box.contains_sqrt {I K : Box} {x : ℝ}
    (hK : K.WellFormed) (hx : I.Contains x) (hg : I.SqrtGate K) :
    K.Contains (Real.sqrt x) := by
  have hI0 : (0:ℝ)≤I.lo := by exact_mod_cast hg.1
  have hK0 : (0:ℝ)≤K.lo := by exact_mod_cast hg.2.1
  have hKl : (K.lo:ℝ)^2≤(I.lo:ℝ) := by exact_mod_cast hg.2.2.1
  have hKu : (I.hi:ℝ)≤(K.hi:ℝ)^2 := by exact_mod_cast hg.2.2.2
  have hKK : (K.lo:ℝ)≤K.hi := by exact_mod_cast hK
  have hx0 : 0≤x := hI0.trans hx.1
  have hs := Real.sq_sqrt hx0
  have hs0 := Real.sqrt_nonneg x
  constructor <;> nlinarith [hx.1, hx.2]

theorem interval_semantics_inverse_sqrt : IntervalInverseSqrtStatement := by
  constructor
  · intro I K x _ _ hx hg
    exact Box.contains_inverse hx hg
  · intro I K x _ hK hx hg
    exact Box.contains_sqrt hK hx hg
#check interval_semantics_inverse_sqrt
#print interval_semantics_inverse_sqrt
#print axioms interval_semantics_inverse_sqrt
end Blueprint.CAP
