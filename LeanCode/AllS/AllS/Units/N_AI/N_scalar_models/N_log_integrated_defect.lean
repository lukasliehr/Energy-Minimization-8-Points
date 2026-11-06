import AllS.Units.N_AI.N_scalar_models.N_exp_integrated_defect

noncomputable section
open scoped BigOperators Interval
namespace Blueprint.CAP

def ScalarLogIntegratedDefectStatement : Prop :=
  ∀ {L : ℕ} (P C : Polynomial ℝ) (r : Fin L→ℝ) (μ : ℝ),
    0<μ → (∀ x∈cellDomain, μ≤P.eval x) →
    C.eval 0 = Real.log (P.eval 0) →
    P*C.derivative-P.derivative = finitePolynomial r →
    ∀ x∈cellDomain, |C.eval x-Real.log (P.eval x)| ≤
      (∑ k, |r k|/(k.val+1))/μ

theorem cellDomain_segment {x u : ℝ} (hx : x∈cellDomain)
    (hu : u∈Set.uIcc 0 x) : u∈cellDomain := by
  rcases le_total (0:ℝ) x with hp | hn
  · rw [Set.uIcc_of_le hp] at hu
    exact ⟨(by norm_num : (-1:ℝ)≤0).trans hu.1, hu.2.trans hx.2⟩
  · rw [Set.uIcc_of_ge hn] at hu
    exact ⟨hx.1.trans hu.1, hu.2.trans (by norm_num : (0:ℝ)≤1)⟩

theorem scalar_models_log_integrated_defect : ScalarLogIntegratedDefectStatement := by
  intro L P C r μ hμ hP hinit hR x hx
  let f : ℝ→ℝ := fun u => (finitePolynomial r).eval u/P.eval u
  have hpos (u : ℝ) (hu : u∈Set.uIcc 0 x) : 0<P.eval u :=
    hμ.trans_le (hP u (cellDomain_segment hx hu))
  have hf : ContinuousOn f (Set.uIcc 0 x) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    exact fun u hu => (hpos u hu).ne'
  have hd (u : ℝ) (hu : u∈Set.uIcc 0 x) :
      HasDerivAt (fun u=>C.eval u-Real.log (P.eval u)) (f u) u := by
    have h := (C.hasDerivAt u).sub ((P.hasDerivAt u).log (hpos u hu).ne')
    convert h using 1 <;> try rfl
    dsimp [f]
    rw [← hR]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul]
    field_simp [(hpos u hu).ne']
  have hint : (∫ u in (0:ℝ)..x, f u) = C.eval x-Real.log (P.eval x) := by
    simpa only [hinit, sub_self, sub_zero] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt hd hf.intervalIntegrable
  have hpoint (u : ℝ) (hu : u∈Set.uIoc 0 x) :
      |f u| ≤ ∑ k, (|r k|/μ)*|u|^k.val := by
    have hu' := Set.uIoc_subset_uIcc hu
    have hp := hpos u hu'
    have hr : |(finitePolynomial r).eval u| ≤ ∑ k, |r k| * |u|^k.val := by
      simp only [finitePolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
      exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by simp [abs_mul, abs_pow])
    have hs : (0:ℝ)≤∑ k, |r k| * |u|^k.val :=
      Finset.sum_nonneg (fun k _=>mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) _))
    dsimp [f]
    rw [abs_div, abs_of_pos hp]
    calc
      _ ≤ (∑ k, |r k| * |u|^k.val)/P.eval u := div_le_div_of_nonneg_right hr hp.le
      _ ≤ (∑ k, |r k| * |u|^k.val)/μ :=
        div_le_div_of_nonneg_left hs hμ (hP u (cellDomain_segment hx hu'))
      _ = ∑ k, (|r k|/μ)*|u|^k.val := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro k _
        ring
  have hb := integral_polynomial_majorant f (fun k=>|r k|/μ)
    (fun k=>div_nonneg (abs_nonneg _) hμ.le) x (abs_le.mpr hx) hf hpoint
  rw [hint] at hb
  calc
    _ ≤ ∑ k, (|r k|/μ)/(k.val+1) := hb
    _ = (∑ k, |r k|/(k.val+1))/μ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      ring

#check scalar_models_log_integrated_defect
#print ScalarLogIntegratedDefectStatement
#print axioms scalar_models_log_integrated_defect
end Blueprint.CAP
