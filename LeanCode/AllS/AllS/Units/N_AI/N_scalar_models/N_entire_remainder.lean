import AllS.Units.N_AI.N_elementary_series.N_exp_tail

noncomputable section
open scoped BigOperators Interval
namespace Blueprint.CAP

def entirePsi (z : ℝ) : ℝ := ∫ u in (0:ℝ)..1, Real.exp (u*z)

def entirePartial (M : ℕ) (z : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (M+1), z^k/(Nat.factorial (k+1):ℝ)

def ScalarEntireRemainderStatement : Prop :=
  ∀ (z : ℝ) (M : ℕ) (K : ℝ), 0≤K →
    (∀ u∈Set.Icc (0:ℝ) 1, Real.exp (u*z)≤K) →
    |entirePsi z-entirePartial M z| ≤ K*|z|^(M+1)/(Nat.factorial (M+2):ℝ)

theorem expTaylor_zero (M : ℕ) : expTaylor M 0=1 := by
  unfold expTaylor
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    simp [hk]
  · simp

theorem expTaylor_lagrange_bound (z u K : ℝ) (M : ℕ) (hu : u∈Set.Icc (0:ℝ) 1)
    (hK : ∀ v∈Set.Icc (0:ℝ) 1, Real.exp (v*z)≤K) :
    |Real.exp (z*u)-expTaylor M (z*u)| ≤
      K*|z|^(M+1)*u^(M+1)/(Nat.factorial (M+1):ℝ) := by
  by_cases hu₀ : u=0
  · subst u
    simp [expTaylor_zero]
  have huPos : 0<u := lt_of_le_of_ne hu.1 (Ne.symm hu₀)
  have htaylor : taylorWithinEval (fun v : ℝ => Real.exp (z*v)) M (Set.uIcc 0 u) 0 u =
      expTaylor M (z*u) := by
    rw [taylor_within_apply]
    unfold expTaylor
    apply Finset.sum_congr rfl
    intro k _
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc huPos.ne)
      (by fun_prop) Set.left_mem_uIcc, iteratedDeriv_exp_const_mul]
    simp only [sub_zero, smul_eq_mul, mul_zero, Real.exp_zero, mul_one, mul_pow]
    ring
  obtain ⟨v,hv,hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f:=fun v : ℝ => Real.exp (z*v)) (n:=M) (x₀:=0) (x:=u) huPos.ne (by fun_prop)
  rw [htaylor, iteratedDeriv_exp_const_mul] at hrem
  simp only [sub_zero] at hrem
  rw [Set.uIoo_of_le hu.1] at hv
  have hK' : Real.exp (z*v)≤K := by
    simpa only [mul_comm] using hK v ⟨hv.1.le,hv.2.le.trans hu.2⟩
  rw [hrem]
  have hfac₀ : (0:ℝ)≤(Nat.factorial (M+1):ℝ) := by positivity
  simp only [abs_div, abs_mul, abs_pow, abs_of_nonneg hu.1,
    abs_of_nonneg hfac₀, abs_of_pos (Real.exp_pos (z*v))]
  calc
    _ ≤ |z|^(M+1)*K*u^(M+1)/(Nat.factorial (M+1):ℝ) := by gcongr
    _ = K*|z|^(M+1)*u^(M+1)/(Nat.factorial (M+1):ℝ) := by ring

theorem integral_expTaylor (z : ℝ) (M : ℕ) :
    (∫ u in (0:ℝ)..1, expTaylor M (z*u)) = entirePartial M z := by
  unfold expTaylor entirePartial
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro k _
    simp only [mul_pow]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_pow]
    simp only [one_pow, zero_pow (Nat.succ_ne_zero k), sub_zero]
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · intro k _
    exact (by fun_prop : Continuous (fun u : ℝ => (z*u)^k/(Nat.factorial k:ℝ))).intervalIntegrable 0 1

theorem scalar_models_entire_remainder : ScalarEntireRemainderStatement := by
  intro z M K hK₀ hK
  let f : ℝ→ℝ := fun u => Real.exp (z*u)-expTaylor M (z*u)
  let B : ℝ := K*|z|^(M+1)/(Nat.factorial (M+1):ℝ)
  have hf : Continuous f := by dsimp [f,expTaylor]; fun_prop
  have hg : Continuous (fun u : ℝ => B*u^(M+1)) := by fun_prop
  have hi : (∫ u in (0:ℝ)..1, f u) = entirePsi z-entirePartial M z := by
    rw [intervalIntegral.integral_sub]
    · rw [integral_expTaylor]
      congr 1
      apply intervalIntegral.integral_congr
      intro u _
      simp only [mul_comm]
    · exact (by fun_prop : Continuous (fun u : ℝ => Real.exp (z*u))).intervalIntegrable 0 1
    · exact (by dsimp [expTaylor]; fun_prop : Continuous (fun u : ℝ => expTaylor M (z*u))).intervalIntegrable 0 1
  rw [← hi]
  calc
    _ ≤ ∫ u in (0:ℝ)..1, |f u| := intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ u in (0:ℝ)..1, B*u^(M+1) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (hf.abs.intervalIntegrable 0 1) (hg.intervalIntegrable 0 1)
      intro u hu
      have h := expTaylor_lagrange_bound z u K M hu hK
      dsimp [f,B]
      convert h using 1 <;> ring
    _ = K*|z|^(M+1)/(Nat.factorial (M+2):ℝ) := by
      rw [intervalIntegral.integral_const_mul, integral_pow]
      simp only [one_pow, zero_pow (by omega : M+1+1≠0), sub_zero]
      dsimp [B]
      have hfac : Nat.factorial (M+2)=(M+2)*Nat.factorial (M+1) := by
        simpa only [Nat.add_assoc, one_add_one_eq_two] using Nat.factorial_succ (M+1)
      rw [hfac]
      push_cast
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem entire_remainder_nonpositive (z : ℝ) (M : ℕ) (hz : z≤0) :
    |entirePsi z-entirePartial M z| ≤ |z|^(M+1)/(Nat.factorial (M+2):ℝ) := by
  have h := scalar_models_entire_remainder z M 1 zero_le_one (fun u hu => by
    calc
      Real.exp (u*z) ≤ Real.exp 0 := Real.exp_le_exp.mpr (mul_nonpos_of_nonneg_of_nonpos hu.1 hz)
      _ = 1 := Real.exp_zero)
  simpa only [one_mul] using h

theorem entire_remainder_small (z : ℝ) (M : ℕ) (hz : z≤1/11) :
    |entirePsi z-entirePartial M z| ≤ (11/10)*|z|^(M+1)/(Nat.factorial (M+2):ℝ) := by
  apply scalar_models_entire_remainder z M (11/10) (by norm_num)
  intro u hu
  have huz : u*z≤1/11 := by
    calc
      u*z ≤ u*(1/11) := mul_le_mul_of_nonneg_left hz hu.1
      _ ≤ 1*(1/11) := mul_le_mul_of_nonneg_right hu.2 (by norm_num)
      _ = 1/11 := one_mul _
  have hbase : Real.exp (1/11:ℝ)≤11/10 := by
    have h := Real.exp_bound_div_one_sub_of_interval (x:=(1/11:ℝ)) (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  exact (Real.exp_le_exp.mpr huz).trans hbase

#check scalar_models_entire_remainder
#print ScalarEntireRemainderStatement
#print axioms scalar_models_entire_remainder
#print axioms entire_remainder_nonpositive
#print axioms entire_remainder_small
end Blueprint.CAP
