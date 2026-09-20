import LeanCode.Monotonic.ScalarDefinitions
/-! The fast tail stays symbolic: Bernoulli reduces exponent 10000 to
exponent 500, then exponent monotonicity reduces it to the small power 20. -/

noncomputable section
open Real Set
namespace SquareAntiprismCounterexample

def eta : ℝ := (19/20)^n

lemma eta_bounds : 0 < eta ∧ eta < 1/1000000 := by
  have hpos : (0:ℝ) < (19/20)^20 := by positivity
  have hbern := one_add_mul_le_pow (a := (1/19:ℝ)) (by norm_num) 20
  have hbase : (2:ℝ) ≤ (20/19)^20 := by
    calc
      _ ≤ 1+(20:ℝ)*(1/19) := by norm_num
      _ ≤ (1+(1/19:ℝ))^20 := by exact_mod_cast hbern
      _ = _ := by congr 1; norm_num
  have hprod : ((20/19:ℝ)^20)*((19/20:ℝ)^20) = 1 := by rw [←mul_pow]; norm_num
  have hhalf : (19/20:ℝ)^20 ≤ 1/2 := by nlinarith
  have hsmall : (19/20:ℝ)^n ≤ (1/2:ℝ)^20 := by
    calc
      _ = ((19/20:ℝ)^20)^500 := by rw [←pow_mul]; rfl
      _ ≤ (1/2:ℝ)^500 := pow_le_pow_left₀ hpos.le hhalf _
      _ ≤ (1/2:ℝ)^20 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num)
  constructor
  · unfold eta; positivity
  · exact lt_of_le_of_lt hsmall (by norm_num)

lemma fast_distance_ratios :
    dStar < dB aStar ∧ dStar / dB aStar < 19/20 ∧
    dStar < dC aStar ∧ dStar / dC aStar < 19/20 ∧
    dStar < dD aStar ∧ dStar / dD aStar < 19/20 := by
  have hs := sqrt_two_bounds
  rcases distance_domains aStar_mem with ⟨ha,hb,hc,hd⟩
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · norm_num [dStar,dB,aStar]
  · norm_num [dStar,dB,aStar]
  · dsimp [dStar,dC,aStar]; linarith
  · rw [div_lt_iff₀ hc.1]; dsimp [dStar,dC,aStar]; linarith
  · dsimp [dStar,dD,aStar]; linarith
  · rw [div_lt_iff₀ hd.1]; dsimp [dStar,dD,aStar]; linarith

lemma fast_tail (t : ℝ) (ht : dStar < t) (hr : dStar/t ≤ 19/20) :
    |h1 t| ≤ ((n:ℝ)/dStar)*eta ∧
    |h2 t| ≤ ((n:ℝ)*((n:ℝ)+1)/dStar^2)*eta := by
  have ht0 : 0 < t := dStar_pos.trans ht
  have hratio : 0 ≤ dStar/t := le_of_lt (div_pos dStar_pos ht0)
  have hp : (dStar/t)^n ≤ eta := pow_le_pow_left₀ hratio hr n
  have hn : 0 ≤ (n:ℝ) := n_pos.le
  have hn' : 0 ≤ (n:ℝ)*((n:ℝ)+1) := by positivity
  have hdiv : (n:ℝ)/t ≤ (n:ℝ)/dStar := div_le_div_of_nonneg_left hn dStar_pos ht.le
  have hdiv' : (n:ℝ)*((n:ℝ)+1)/t^2 ≤ (n:ℝ)*((n:ℝ)+1)/dStar^2 :=
    div_le_div_of_nonneg_left hn' (sq_pos_of_pos dStar_pos) (by nlinarith [dStar_pos])
  constructor
  · rw [h1,abs_mul,abs_neg,abs_of_nonneg (div_nonneg hn ht0.le),abs_of_nonneg (pow_nonneg hratio _)]
    exact mul_le_mul hdiv hp (pow_nonneg hratio _) (div_nonneg hn dStar_pos.le)
  · rw [h2,abs_mul,abs_of_nonneg (div_nonneg hn' (sq_nonneg _)),abs_of_nonneg (pow_nonneg hratio _)]
    exact mul_le_mul hdiv' hp (pow_nonneg hratio _) (div_nonneg hn' (sq_nonneg _))

lemma h1_at_dStar : h1 dStar = -(n:ℝ)/dStar := by
  simp [h1,ne_of_gt dStar_pos,neg_div]

end SquareAntiprismCounterexample
