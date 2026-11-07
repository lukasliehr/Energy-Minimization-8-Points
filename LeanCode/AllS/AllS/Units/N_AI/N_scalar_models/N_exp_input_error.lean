import AllS.Units.N_AI.N_scalar_models.N_exp_integrated_defect

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def ScalarExpInputErrorStatement : Prop :=
  ∀ {n L : ℕ} (M R : TM n) (f : ℝ→ℝ) (a : M.Witness f)
    (c : Fin (n+1)→ℝ) (r : Fin L→ℝ),
    R.CoeffContains c →
    (finitePolynomial c).eval 0 = Real.exp ((finitePolynomial a.coeff).eval 0) →
    (finitePolynomial c).derivative - (finitePolynomial a.coeff).derivative*
      finitePolynomial c = finitePolynomial r →
    Real.exp (coefficientVariation a.coeff)*(∑ k, |r k|/(k.val+1)) +
      Real.exp (a.coeff 0+coefficientVariation a.coeff+(M.error:ℝ))*(M.error:ℝ) ≤
      (R.error:ℝ) → R.Valid (fun x=>Real.exp (f x))

theorem abs_exp_sub_le_mul (x y A : ℝ) (hx : x≤A) (hy : y≤A) :
    |Real.exp x-Real.exp y| ≤ Real.exp A*|x-y| := by
  have hd (u : ℝ) (_ : u∈Set.Iic A) :
      HasDerivWithinAt Real.exp (Real.exp u) (Set.Iic A) u :=
    (Real.hasDerivAt_exp u).hasDerivWithinAt
  have hb (u : ℝ) (hu : u∈Set.Iic A) : ‖Real.exp u‖≤Real.exp A := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr hu
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Iic A) hy hx

theorem scalar_models_exp_input_error : ScalarExpInputErrorStatement := by
  intro n L M R f a c r hc hinit hR he
  have heM : (0:ℝ)≤M.error := by exact_mod_cast a.error_nonneg
  have hD : (0:ℝ)≤∑ k, |r k|/(k.val+1) :=
    Finset.sum_nonneg (fun k _=>div_nonneg (abs_nonneg _) (by positivity))
  have hR₀ : (0:ℝ)≤R.error :=
    (add_nonneg (mul_nonneg (Real.exp_pos _).le hD)
      (mul_nonneg (Real.exp_pos _).le heM)).trans he
  refine ⟨by exact_mod_cast hR₀, c, hc, ?_⟩
  intro x hx
  have hPupper : scalarEval a.coeff x≤a.coeff 0+coefficientVariation a.coeff := by
    have h := (scalar_models_segment_variation a.coeff x 0 hx Set.left_mem_uIcc).2
    have := (abs_le.mp h).2
    linarith
  have hFupper : f x≤a.coeff 0+coefficientVariation a.coeff+(M.error:ℝ) := by
    have := (abs_le.mp (a.remainder x hx)).2
    linarith
  have herr := (abs_exp_sub_le_mul (f x) (scalarEval a.coeff x)
    (a.coeff 0+coefficientVariation a.coeff+(M.error:ℝ)) hFupper (by linarith)).trans
      (mul_le_mul_of_nonneg_left (a.remainder x hx) (Real.exp_pos _).le)
  have hV (y : ℝ) (hy : y∈cellDomain) (u : ℝ) (hu : u∈Set.uIcc 0 y) :
      (finitePolynomial a.coeff).eval y-(finitePolynomial a.coeff).eval u ≤
        coefficientVariation a.coeff := by
    rw [finitePolynomial_eval, finitePolynomial_eval]
    exact (le_abs_self _).trans (scalarEval_segment_bound a.coeff y u hy hu)
  have hdef := scalar_models_exp_integrated_defect (finitePolynomial a.coeff)
    (finitePolynomial c) r (coefficientVariation a.coeff) hinit hR hV x hx
  rw [finitePolynomial_eval, finitePolynomial_eval] at hdef
  calc
    |Real.exp (f x)-scalarEval c x| =
        |(Real.exp (f x)-Real.exp (scalarEval a.coeff x)) +
          (Real.exp (scalarEval a.coeff x)-scalarEval c x)| := by congr 1; ring
    _ ≤ |Real.exp (f x)-Real.exp (scalarEval a.coeff x)| +
        |Real.exp (scalarEval a.coeff x)-scalarEval c x| := abs_add_le _ _
    _ ≤ Real.exp (a.coeff 0+coefficientVariation a.coeff+(M.error:ℝ))*(M.error:ℝ) +
        Real.exp (coefficientVariation a.coeff)*(∑ k, |r k|/(k.val+1)) := add_le_add herr hdef
    _ = Real.exp (coefficientVariation a.coeff)*(∑ k, |r k|/(k.val+1)) +
        Real.exp (a.coeff 0+coefficientVariation a.coeff+(M.error:ℝ))*(M.error:ℝ) := add_comm _ _
    _ ≤ (R.error:ℝ) := he

#check scalar_models_exp_input_error
#print ScalarExpInputErrorStatement
#print axioms scalar_models_exp_input_error
end Blueprint.CAP
