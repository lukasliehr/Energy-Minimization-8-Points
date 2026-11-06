import AllS.Units.N_AI.N_scalar_models.N_log_integrated_defect

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def ScalarLogInputErrorStatement : Prop :=
  ∀ {n L : ℕ} (M R : TM n) (f : ℝ→ℝ) (a : M.Witness f)
    (c : Fin (n+1)→ℝ) (r : Fin L→ℝ) (I : Box) (μ : ℚ),
    M.CommonPositiveHull I μ → R.CoeffContains c →
    (finitePolynomial c).eval 0 = Real.log ((finitePolynomial a.coeff).eval 0) →
    finitePolynomial a.coeff*(finitePolynomial c).derivative -
      (finitePolynomial a.coeff).derivative = finitePolynomial r →
    ((∑ k, |r k|/(k.val+1))+(M.error:ℝ))/(μ:ℝ) ≤ (R.error:ℝ) →
    R.Valid (fun x=>Real.log (f x))

theorem abs_log_sub_le_div (x y μ : ℝ) (hμ : 0<μ) (hx : μ≤x) (hy : μ≤y) :
    |Real.log x-Real.log y| ≤ |x-y|/μ := by
  have hd (u : ℝ) (hu : u∈Set.Ici μ) :
      HasDerivWithinAt Real.log (1/u) (Set.Ici μ) u := by
    simpa only [one_div] using (Real.hasDerivAt_log (hμ.trans_le hu).ne').hasDerivWithinAt
  have hb (u : ℝ) (hu : u∈Set.Ici μ) : ‖(1:ℝ)/u‖≤1/μ := by
    rw [Real.norm_eq_abs, abs_div, abs_one, abs_of_pos (hμ.trans_le hu)]
    exact one_div_le_one_div_of_le hμ hu
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Ici μ) hy hx
  simpa only [Real.norm_eq_abs, one_div_mul_eq_div] using h

theorem scalar_models_log_input_error : ScalarLogInputErrorStatement := by
  intro n L M R f a c r I μ hHull hc hinit hR he
  have hμ : (0:ℝ)<μ := by exact_mod_cast hHull.1
  have hμI : (μ:ℝ)≤I.lo := by exact_mod_cast hHull.2.1
  have heM : (0:ℝ)≤M.error := by exact_mod_cast a.error_nonneg
  have hP (x : ℝ) (hx : x∈cellDomain) : (μ:ℝ)≤(finitePolynomial a.coeff).eval x := by
    have h := hHull.2.2 a.coeff a.coeff_mem x hx 0 (by simpa using heM)
    rw [finitePolynomial_eval]
    exact hμI.trans (by simpa using h.1)
  have hF (x : ℝ) (hx : x∈cellDomain) : (μ:ℝ)≤f x := by
    have h := hHull.2.2 a.coeff a.coeff_mem x hx
      (f x-scalarEval a.coeff x) (a.remainder x hx)
    exact hμI.trans (by simpa only [add_sub_cancel] using h.1)
  have hD : (0:ℝ)≤∑ k, |r k|/(k.val+1) :=
    Finset.sum_nonneg (fun k _ => div_nonneg (abs_nonneg _) (by positivity))
  have hR₀ : (0:ℝ)≤R.error := (div_nonneg (add_nonneg hD heM) hμ.le).trans he
  refine ⟨by exact_mod_cast hR₀, c, hc, ?_⟩
  intro x hx
  have hdef := scalar_models_log_integrated_defect (finitePolynomial a.coeff)
    (finitePolynomial c) r μ hμ hP hinit hR x hx
  rw [finitePolynomial_eval, finitePolynomial_eval, abs_sub_comm] at hdef
  have herr := abs_log_sub_le_div (f x) (scalarEval a.coeff x) μ hμ (hF x hx)
    (by simpa only [finitePolynomial_eval] using hP x hx)
  have herr' := herr.trans (div_le_div_of_nonneg_right (a.remainder x hx) hμ.le)
  calc
    |Real.log (f x)-scalarEval c x| =
        |(Real.log (f x)-Real.log (scalarEval a.coeff x)) +
          (Real.log (scalarEval a.coeff x)-scalarEval c x)| := by congr 1; ring
    _ ≤ |Real.log (f x)-Real.log (scalarEval a.coeff x)| +
        |Real.log (scalarEval a.coeff x)-scalarEval c x| := abs_add_le _ _
    _ ≤ (M.error:ℝ)/(μ:ℝ)+(∑ k, |r k|/(k.val+1))/(μ:ℝ) := add_le_add herr' hdef
    _ = ((∑ k, |r k|/(k.val+1))+(M.error:ℝ))/(μ:ℝ) := by ring
    _ ≤ (R.error:ℝ) := he

#check scalar_models_log_input_error
#print ScalarLogInputErrorStatement
#print axioms scalar_models_log_input_error
end Blueprint.CAP
