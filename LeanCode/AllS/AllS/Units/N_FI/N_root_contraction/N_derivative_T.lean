import AllS.Units.N_FI.N_root_contraction.N_coordinates

noncomputable section
open Real
namespace Blueprint.Thomson.Finite

def rootTDeriv (q v : ℝ) : ℝ :=
  -rootBeta*exp (v/q)*exp (-q*log (sqrt 2+exp (v/q)))/
    ((sqrt 2+exp (v/q))*(1+exp (-q*log 2)-rootBeta*exp (-q*log (sqrt 2+exp (v/q)))))

theorem rootT_hasDerivAt (q v : ℝ) (hq : 0 < q) (hv : 0 ≤ v) :
    HasDerivAt (rootT q) (rootTDeriv q v) v := by
  have hu := ((hasDerivAt_id v).div_const q).exp
  have hz := hu.const_add (sqrt 2)
  have hzpos : 0 < sqrt 2+exp (v/q) := by positivity
  have he := ((hz.log hzpos.ne').const_mul (-q)).exp
  have hd := (hasDerivAt_const v (1+exp (-q*log 2))).sub (he.const_mul rootBeta)
  have hu1 : 1 ≤ exp (v/q) := Real.one_le_exp (div_nonneg hv hq.le)
  have hδ := rootT_delta_pos q (exp (v/q)) hq hu1
  have hden : 1+exp (-q*log 2)-rootBeta*exp (-q*log (sqrt 2+exp (v/q))) ≠ 0 := by linarith
  have ht := (hd.log hden).const_sub rootC
  convert! ht using 1
  dsimp [rootTDeriv]
  field_simp
  ring

theorem rootT_factor_bound (u : ℝ) (hu : 0 < u) :
    0 ≤ rootBeta*u/(sqrt 2+u)^2 ∧ rootBeta*u/(sqrt 2+u)^2 ≤ 1/19 := by
  have hr := root_sqrt_bounds
  have hrsq := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hb := root_constants.2.1
  have hz : 0 < sqrt 2+u := by positivity
  constructor
  · positivity
  · apply (div_le_iff₀ (sq_pos_of_pos hz)).mpr
    dsimp [rootBeta]
    have hquad := sq_nonneg (u-sqrt 2)
    have hrat : 0 < 4*sqrt (2:ℝ)-19*(1-sqrt 2/2) := by nlinarith
    nlinarith [mul_pos hu hrat]

theorem rootT_exponent_bound (q u : ℝ) (m : ℕ) (hm : 1 ≤ m) (hmq : (m:ℝ) ≤ q)
    (hu : 1 ≤ u) : exp ((1-q)*log (sqrt 2+u)) ≤ (5/12:ℝ)^(m-1) := by
  have hqm : 1 ≤ q := le_trans (by exact_mod_cast hm) hmq
  have hz : (12/5:ℝ) ≤ sqrt 2+u := by linarith [root_sqrt_bounds.1]
  have hl : log (12/5:ℝ) ≤ log (sqrt 2+u) := Real.log_le_log (by norm_num) hz
  have hl0 : 0 ≤ log (12/5:ℝ) := Real.log_nonneg (by norm_num)
  have hmcast : ((m-1:ℕ):ℝ)=(m:ℝ)-1 := by rw [Nat.cast_sub hm]; norm_num
  have hpow : exp (-((m-1:ℕ):ℝ)*log (12/5:ℝ))=(5/12:ℝ)^(m-1) := by
    rw [neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<12/5),← inv_pow]
    norm_num
  rw [← hpow]
  apply Real.exp_le_exp.mpr
  rw [hmcast]
  have h1 := mul_le_mul_of_nonpos_left hl (show 1-q ≤ 0 by linarith)
  have h2 := mul_le_mul_of_nonneg_right (show 1-q ≤ -((m:ℝ)-1) by linarith) hl0
  linarith

theorem rootT_derivative_bound (q v : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hmq : (m:ℝ) ≤ q) (hv : 0 ≤ v) :
    HasDerivAt (rootT q) (rootTDeriv q v) v ∧ |rootTDeriv q v| ≤ rootLambda m := by
  have hq : 0 < q := by
    have : (1:ℝ) ≤ m := by exact_mod_cast hm
    linarith
  let u := exp (v/q)
  let z := sqrt 2+u
  let δ := exp (-q*log 2)-rootBeta*exp (-q*log z)
  have hu : 0 < u := Real.exp_pos _
  have hu1 : 1 ≤ u := Real.one_le_exp (div_nonneg hv hq.le)
  have hz : 0 < z := by dsimp [z]; positivity
  have hd : 0 < δ := rootT_delta_pos q u hq hu1
  have hD : 0 < 1+δ := by linarith
  have hb : 0 < rootBeta := root_constants.2.1
  have he : exp ((1-q)*log z)=z*exp (-q*log z) := by
    rw [sub_mul,one_mul,sub_eq_add_neg,Real.exp_add,Real.exp_log hz]
    congr 1
    ring
  have hfactor : |rootTDeriv q v|=(rootBeta*u/z^2)*exp ((1-q)*log z)/(1+δ) := by
    have hneg : rootTDeriv q v < 0 := by
      change -rootBeta*u*exp (-q*log z)/(z*(1+exp (-q*log 2)-rootBeta*exp (-q*log z))) < 0
      rw [add_sub_assoc]
      exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hb) hu) (Real.exp_pos _)) (mul_pos hz hD)
    rw [abs_of_neg hneg,he]
    dsimp [rootTDeriv,u,z,δ]
    field_simp
    ring
  refine ⟨rootT_hasDerivAt q v hq hv,?_⟩
  rw [hfactor]
  have hf := rootT_factor_bound u hu
  have hg := rootT_exponent_bound q u m hm hmq hu1
  have hprod : (rootBeta*u/z^2)*exp ((1-q)*log z) ≤ rootLambda m :=
    mul_le_mul hf.2 hg (Real.exp_pos _).le (by norm_num)
  apply (div_le_iff₀ hD).mpr
  have hl : 0 ≤ rootLambda m := by unfold rootLambda; positivity
  nlinarith

theorem rootLambda_bounds (m : ℕ) : 0 < rootLambda m ∧ rootLambda m < 1 := by
  have hp : (5/12:ℝ)^(m-1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  constructor
  · unfold rootLambda; positivity
  · unfold rootLambda; nlinarith

theorem root_contraction_derivative_T (q q₀ v : ℝ) (hq₀ : 1 ≤ q₀) (hq : q₀ ≤ q)
    (hv : v ∈ Set.Icc 0 rootC) :
    HasDerivAt (rootT q) (rootTDeriv q v) v ∧
      |rootTDeriv q v| ≤ rootLambda ⌊q₀⌋₊ ∧ rootLambda ⌊q₀⌋₊ < 1 := by
  obtain ⟨hd,hb⟩ := rootT_derivative_bound q v ⌊q₀⌋₊ (Nat.le_floor (by simpa using hq₀))
    ((Nat.floor_le (by linarith : 0 ≤ q₀)).trans hq) hv.1
  exact ⟨hd,hb,(rootLambda_bounds _).2⟩

#check root_contraction_derivative_T
#print axioms root_contraction_derivative_T
end Blueprint.Thomson.Finite
