import AllS.Units.N_AI.N_scalar_models.N_cauchy_low_high
import AllS.Units.N_AI.N_scalar_models.N_segment_variation

noncomputable section
open scoped BigOperators Interval
open MeasureTheory
namespace Blueprint.CAP

def ScalarExpIntegratedDefectStatement : Prop :=
  ∀ {L : ℕ} (P C : Polynomial ℝ) (r : Fin L→ℝ) (V : ℝ),
    C.eval 0 = Real.exp (P.eval 0) →
    C.derivative-P.derivative*C = finitePolynomial r →
    (∀ x∈cellDomain, ∀ u∈Set.uIcc 0 x, P.eval x-P.eval u ≤ V) →
    ∀ x∈cellDomain, |Real.exp (P.eval x)-C.eval x| ≤
      Real.exp V * ∑ k, |r k|/(k.val+1)

theorem integral_polynomial_majorant {L : ℕ} (f : ℝ→ℝ) (c : Fin L→ℝ)
    (hc : ∀ k, 0≤c k) (x : ℝ) (hx : |x|≤1)
    (hf : ContinuousOn f (Set.uIcc 0 x))
    (hbound : ∀ u∈Set.uIoc 0 x, |f u| ≤ ∑ k, c k*|u|^k.val) :
    |∫ u in (0:ℝ)..x, f u| ≤ ∑ k, c k/(k.val+1) := by
  have hterm (k : Fin L) : Continuous (fun u : ℝ => c k*|u|^k.val) := by fun_prop
  have hsum : Continuous (fun u : ℝ => ∑ k, c k*|u|^k.val) := by fun_prop
  calc
    |∫ u in (0:ℝ)..x, f u| ≤ ∫ u in Set.uIoc (0:ℝ) x, |f u| := by
      simpa only [Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_integral_norm_uIoc (f:=f) (a:=0) (b:=x))
    _ ≤ ∫ u in Set.uIoc (0:ℝ) x, ∑ k, c k*|u|^k.val :=
      setIntegral_mono_on (hf.abs.integrableOn_uIcc.mono_set Set.uIoc_subset_uIcc) hsum.integrableOn_uIoc
        measurableSet_uIoc hbound
    _ = ∑ k, ∫ u in Set.uIoc (0:ℝ) x, c k*|u|^k.val :=
      integral_finsetSum _ (fun k _ => (hterm k).integrableOn_uIoc)
    _ = ∑ k, c k*(|x|^(k.val+1)/(k.val+1)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [integral_const_mul]
      congr 1
      simpa only [sub_zero, Nat.cast_add, Nat.cast_one] using
        (integral_pow_abs_sub_uIoc (a:=0) (b:=x) (n:=k.val))
    _ ≤ ∑ k, c k/(k.val+1) := by
      apply Finset.sum_le_sum
      intro k _
      have hp : |x|^(k.val+1)≤1 := pow_le_one₀ (abs_nonneg x) hx
      have hd : (0:ℝ)<k.val+1 := by positivity
      calc
        c k*(|x|^(k.val+1)/(k.val+1)) ≤ c k*(1/(k.val+1)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hp hd.le) (hc k)
        _ = c k/(k.val+1) := by ring

theorem scalar_models_exp_integrated_defect : ScalarExpIntegratedDefectStatement := by
  intro L P C r V hinit hR hV x hx
  let f : ℝ→ℝ := fun u => Real.exp (P.eval x-P.eval u)*(finitePolynomial r).eval u
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hd (u : ℝ) : HasDerivAt
      (fun u=>Real.exp (P.eval x-P.eval u)*C.eval u) (f u) u := by
    have h := (((hasDerivAt_const u (P.eval x)).sub (P.hasDerivAt u)).exp).mul (C.hasDerivAt u)
    convert h using 1 <;> try rfl
    dsimp [f]
    rw [← hR]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul]
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hd u) (hf.intervalIntegrable 0 x)
  have hstart : Real.exp (P.eval x-P.eval 0)*C.eval 0 = Real.exp (P.eval x) := by
    rw [hinit, Real.exp_sub]
    exact div_mul_cancel₀ _ (Real.exp_ne_zero _)
  have hint : (∫ u in (0:ℝ)..x, f u) = C.eval x-Real.exp (P.eval x) := by
    simpa only [sub_self, Real.exp_zero, one_mul, hstart] using hFTC
  have hpoint (u : ℝ) (hu : u∈Set.uIoc 0 x) :
      |f u| ≤ ∑ k, (Real.exp V * |r k|) * |u|^k.val := by
    have he := Real.exp_le_exp.mpr (hV x hx u (Set.uIoc_subset_uIcc hu))
    have hr : |(finitePolynomial r).eval u| ≤ ∑ k, |r k| * |u|^k.val := by
      simp only [finitePolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
      exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by simp [abs_mul, abs_pow])
    dsimp [f]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp V*(∑ k, |r k| * |u|^k.val) :=
        mul_le_mul he hr (abs_nonneg _) (Real.exp_pos _).le
      _ = ∑ k, (Real.exp V * |r k|) * |u|^k.val := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
  have hb := integral_polynomial_majorant f (fun k=>Real.exp V*|r k|)
    (fun k=>mul_nonneg (Real.exp_pos _).le (abs_nonneg _)) x (abs_le.mpr hx) hf.continuousOn hpoint
  rw [hint, abs_sub_comm] at hb
  calc
    _ ≤ ∑ k, (Real.exp V*|r k|)/(k.val+1) := hb
    _ = Real.exp V*∑ k, |r k|/(k.val+1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

#check scalar_models_exp_integrated_defect
#print ScalarExpIntegratedDefectStatement
#print axioms scalar_models_exp_integrated_defect
end Blueprint.CAP
