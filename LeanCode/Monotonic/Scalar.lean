import LeanCode.Monotonic.ScalarDefinitions

noncomputable section
open Real Set Filter
open scoped BigOperators ContDiff Topology
namespace SquareAntiprismCounterexample

/-- Shifted reciprocal natural power; derivative identities are local to positive denominators. -/
def reciprocalPower (c : ℝ) (m : ℕ) (t : ℝ) : ℝ := 1 / (c+t)^m

lemma reciprocalPower_derivative (c : ℝ) (m : ℕ) {t : ℝ} (ht : 0 < c+t) :
    HasDerivAt (reciprocalPower c m) (-(m:ℝ) / (c+t)^(m+1)) t := by
  have he : -(m:ℤ)-1 = -((m+1:ℕ):ℤ) := by omega
  have hd := (hasDerivAt_zpow (-(m:ℤ)) (c+t) (Or.inl ht.ne')).comp t
    ((hasDerivAt_id t).const_add c)
  change HasDerivAt (fun t => 1 / (c+t)^m) _ t
  simpa only [Function.comp_def, Int.cast_neg, Int.cast_natCast,
    he, zpow_neg, zpow_natCast, mul_one, div_eq_mul_inv, one_mul] using hd

lemma reciprocalPower_smooth (c : ℝ) (m : ℕ) (hc : 0 ≤ c) :
    ContDiffOn ℝ ∞ (reciprocalPower c m) (Ioi 0) := by
  change ContDiffOn ℝ ∞ (fun t => 1 / (c+t)^m) (Ioi 0)
  simpa only [one_div] using!
    (((contDiff_const.add contDiff_id).contDiffOn :
      ContDiffOn ℝ ∞ (fun t : ℝ => c+t) (Ioi 0)).pow m).inv
      (fun t ht => pow_ne_zero m (ne_of_gt (add_pos_of_nonneg_of_pos hc ht)))

lemma reciprocalPower_iterated (c : ℝ) (m k : ℕ) {t : ℝ} (ht : 0 < c+t) :
    iteratedDeriv k (reciprocalPower c m) t =
      (-1:ℝ)^k * (m.ascFactorial k : ℝ) * reciprocalPower c (m+k) t := by
  induction k generalizing t with
  | zero => simp [reciprocalPower]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv k (reciprocalPower c m) =ᶠ[nhds t]
        (fun x => (-1:ℝ)^k * (m.ascFactorial k : ℝ) * reciprocalPower c (m+k) x) := by
      have hn : ∀ᶠ x in nhds t, 0 < c+x :=
        continuousAt_const.eventually_lt (continuousAt_const.add continuousAt_id) ht
      filter_upwards [hn] with x hx
      exact ih hx
    rw [he.deriv_eq]
    rw [((reciprocalPower_derivative c (m+k) ht).const_mul
      ((-1:ℝ)^k * (m.ascFactorial k : ℝ))).deriv]
    simp only [reciprocalPower, Nat.ascFactorial_succ, Nat.cast_mul, Nat.cast_add,
      pow_succ, Nat.add_assoc]
    ring

lemma reciprocalPower_signed_pos (c : ℝ) {m : ℕ} (hm : 0 < m) (k : ℕ)
    {t : ℝ} (ht : 0 < c+t) :
    0 < (-1:ℝ)^k * iteratedDeriv k (reciprocalPower c m) t := by
  rw [reciprocalPower_iterated c m k ht]
  have hp : (0:ℝ) < m.ascFactorial k := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    exact_mod_cast Nat.ascFactorial_pos j k
  have hr : 0 < reciprocalPower c (m+k) t := by unfold reciprocalPower; positivity
  have hs : (-1:ℝ)^k * (-1:ℝ)^k = 1 := by
    rw [← mul_pow]; norm_num
  calc
    0 < (m.ascFactorial k : ℝ) * reciprocalPower c (m+k) t := mul_pos hp hr
    _ = _ := by calc
      _ = ((-1:ℝ)^k * (-1:ℝ)^k) *
          ((m.ascFactorial k : ℝ) * reciprocalPower c (m+k) t) := by rw [hs]; ring
      _ = _ := by ring

lemma g_as_reciprocal : g = reciprocalPower (n:ℝ) 1 := by
  funext t; simp [g, reciprocalPower]
lemma h_as_reciprocal : h = fun t => dStar^n * reciprocalPower 0 n t := by
  funext t
  simp only [h, div_pow]
  simp only [reciprocalPower, zero_add, div_eq_mul_inv]
  ring

lemma g1_as_reciprocal : g1 = fun t => -reciprocalPower (n:ℝ) 2 t := by
  funext t; simp [g1, reciprocalPower, div_eq_mul_inv]
lemma g2_as_reciprocal : g2 = fun t => 2 * reciprocalPower (n:ℝ) 3 t := by
  funext t; simp [g2, reciprocalPower, div_eq_mul_inv]
lemma h1_as_reciprocal :
    h1 = fun t => -((n:ℝ) * dStar^n) * reciprocalPower 0 (n+1) t := by
  funext t
  simp only [h1, reciprocalPower, zero_add, pow_succ, div_eq_mul_inv,
    mul_inv_rev, one_mul]
  ring
lemma h2_as_reciprocal :
    h2 = fun t => ((n:ℝ) * ((n:ℝ)+1) * dStar^n) * reciprocalPower 0 (n+2) t := by
  funext t
  simp only [h2, reciprocalPower, zero_add, pow_add, div_eq_mul_inv,
    mul_inv_rev, one_mul]
  ring

lemma g_hasDerivAt {t : ℝ} (ht : 0 < t) : HasDerivAt g (g1 t) t := by
  rw [g_as_reciprocal]
  simpa [g1] using reciprocalPower_derivative (n:ℝ) 1 (show 0 < (n:ℝ)+t by linarith [n_pos])
lemma g1_hasDerivAt {t : ℝ} (ht : 0 < t) : HasDerivAt g1 (g2 t) t := by
  rw [g1_as_reciprocal]
  simpa only [g2, Nat.cast_ofNat, Nat.reduceAdd, neg_div, neg_neg] using!
    (reciprocalPower_derivative (n:ℝ) 2
    (show 0 < (n:ℝ)+t by linarith [n_pos])).fun_neg
lemma h_hasDerivAt {t : ℝ} (ht : 0 < t) : HasDerivAt h (h1 t) t := by
  rw [h_as_reciprocal, h1_as_reciprocal]
  convert! (reciprocalPower_derivative 0 n (by simpa using ht)).const_mul (dStar^n) using 1
  all_goals try dsimp [reciprocalPower]
  all_goals ring
lemma h1_hasDerivAt {t : ℝ} (ht : 0 < t) : HasDerivAt h1 (h2 t) t := by
  rw [h1_as_reciprocal, h2_as_reciprocal]
  convert! (reciprocalPower_derivative 0 (n+1) (by simpa using ht)).const_mul
    (-((n:ℝ) * dStar^n)) using 1
  all_goals try dsimp [reciprocalPower]
  all_goals try push_cast
  all_goals ring
lemma f_hasDerivAt {t : ℝ} (ht : 0 < t) : HasDerivAt f (f1 t) t :=
  (g_hasDerivAt ht).add ((h_hasDerivAt ht).const_mul lambda)
lemma f1_hasDerivAt {t : ℝ} (ht : 0 < t) : HasDerivAt f1 (f2 t) t :=
  (g1_hasDerivAt ht).add ((h1_hasDerivAt ht).const_mul lambda)

lemma g_smooth : ContDiffOn ℝ ∞ g (Ioi 0) := by
  rw [g_as_reciprocal]
  exact reciprocalPower_smooth _ _ n_pos.le
lemma h_smooth : ContDiffOn ℝ ∞ h (Ioi 0) := by
  rw [h_as_reciprocal]
  exact contDiff_const.contDiffOn.mul (reciprocalPower_smooth 0 n le_rfl)
lemma f_smooth : ContDiffOn ℝ ∞ f (Ioi 0) := by
  exact g_smooth.add (contDiff_const.contDiffOn.mul h_smooth)

lemma g2_smooth : ContDiffOn ℝ ∞ g2 (Ioi 0) := by
  rw [g2_as_reciprocal]
  exact contDiff_const.contDiffOn.mul (reciprocalPower_smooth _ _ n_pos.le)
lemma h2_smooth : ContDiffOn ℝ ∞ h2 (Ioi 0) := by
  rw [h2_as_reciprocal]
  exact contDiff_const.contDiffOn.mul (reciprocalPower_smooth 0 (n+2) le_rfl)
lemma f2_continuous : ContinuousOn f2 (Ioi 0) :=
  (g2_smooth.add (contDiff_const.contDiffOn.mul h2_smooth)).continuousOn
lemma f2_pos (hLambda : 0 < lambda) {t : ℝ} (ht : 0 < t) : 0 < f2 t := by
  have hnt : 0 < (n:ℝ)+t := by linarith [n_pos]
  have hg : 0 < g2 t := by unfold g2; positivity
  have hh : 0 < h2 t := by
    unfold h2
    exact mul_pos (div_pos (mul_pos n_pos (by linarith [n_pos]))
      (sq_pos_of_pos ht)) (pow_pos (div_pos dStar_pos ht) _)
  exact add_pos hg (mul_pos hLambda hh)

lemma g_signed_pos (k : ℕ) {t : ℝ} (ht : 0 < t) :
    0 < (-1:ℝ)^k * iteratedDeriv k g t := by
  rw [g_as_reciprocal]
  exact reciprocalPower_signed_pos _ (by norm_num) k (by linarith [n_pos])
lemma h_signed_pos (k : ℕ) {t : ℝ} (ht : 0 < t) :
    0 < (-1:ℝ)^k * iteratedDeriv k h t := by
  rw [h_as_reciprocal, iteratedDeriv_const_mul_field]
  have hp := reciprocalPower_signed_pos 0 (show 0 < n by norm_num [n]) k (by simpa using ht)
  have hd := pow_pos dStar_pos n
  nlinarith [mul_pos hd hp]

lemma f_strictCM (hLambda : 0 < lambda) : StrictlyCompletelyMonotone f := by
  refine ⟨f_smooth, ?_⟩
  intro k t ht
  have hg : ContDiffAt ℝ k g t :=
    (g_smooth.contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by exact_mod_cast le_top)
  have hh : ContDiffAt ℝ k h t :=
    (h_smooth.contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by exact_mod_cast le_top)
  change 0 < (-1:ℝ)^k * iteratedDeriv k (fun t => g t + lambda * h t) t
  rw [iteratedDeriv_fun_add hg (contDiffAt_const.mul hh), iteratedDeriv_const_mul_field]
  nlinarith [g_signed_pos k ht, h_signed_pos k ht,
    mul_pos hLambda (h_signed_pos k ht)]

lemma h_tendsto_zero : Tendsto h (nhdsWithin 0 (Ioi 0)) atTop := by
  change Tendsto (fun t => (dStar/t)^n) (nhdsWithin 0 (Ioi 0)) atTop
  have hi : Tendsto (fun t : ℝ => t⁻¹) (nhdsWithin 0 (Ioi 0)) atTop :=
    tendsto_inv_nhdsGT_zero
  have hd := hi.const_mul_atTop dStar_pos
  simpa only [h, Function.comp_def, div_eq_mul_inv] using
    (tendsto_pow_atTop (show n ≠ 0 by norm_num [n])).comp hd

lemma f_tendsto_zero (hLambda : 0 < lambda) :
    Tendsto f (nhdsWithin 0 (Ioi 0)) atTop := by
  apply tendsto_atTop_mono' _ _ (h_tendsto_zero.const_mul_atTop hLambda)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hg : 0 < g t := by unfold g; exact one_div_pos.mpr (add_pos n_pos ht)
  dsimp [f]
  linarith

end SquareAntiprismCounterexample
