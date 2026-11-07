import AllS.Units.N_AI.N_scalar_models.N_cauchy_low_high

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def ScalarProductErrorStatement : Prop :=
  ∀ {n : ℕ} (M₁ M₂ R : TM n) (f g : ℝ→ℝ)
    (a : M₁.Witness f) (b : M₂.Witness g) (A B T : ℝ),
    (∑ k, |a.coeff k|) ≤ A → (∑ k, |b.coeff k|) ≤ B →
    (∀ x ∈ cellDomain, |x^(n+1)*(cauchyHigh a.coeff b.coeff).eval x| ≤ T) →
    R.CoeffContains (cauchyLow a.coeff b.coeff) →
    T+(M₁.error:ℝ)*B+(M₂.error:ℝ)*A+(M₁.error:ℝ)*(M₂.error:ℝ) ≤ (R.error:ℝ) →
    R.Valid (fun x=>f x*g x)

theorem scalarEval_abs_le_sum {n : ℕ} (a : Fin (n+1)→ℝ) (x : ℝ)
    (hx : x∈cellDomain) : |scalarEval a x| ≤ ∑ k, |a k| := by
  have hxabs : |x|≤1 := abs_le.mpr hx
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro k _
  rw [abs_mul, abs_pow]
  exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg x) hxabs) (abs_nonneg (a k))).trans_eq (mul_one _)

theorem abs_add_four_le (a b c d : ℝ) :
    |a+b+c+d| ≤ |a|+|b|+|c|+|d| := by
  calc
    |a+b+c+d| ≤ |a+b+c|+|d| := abs_add_le _ _
    _ ≤ (|a+b|+|c|)+|d| := add_le_add (abs_add_le (a+b) c) le_rfl
    _ ≤ (|a|+|b|+|c|)+|d| := add_le_add (add_le_add (abs_add_le a b) le_rfl) le_rfl

theorem scalar_models_product_error : ScalarProductErrorStatement := by
  intro n M₁ M₂ R f g a b A B T hA hB hT hc he
  have he₁ : (0:ℝ)≤M₁.error := by exact_mod_cast a.error_nonneg
  have he₂ : (0:ℝ)≤M₂.error := by exact_mod_cast b.error_nonneg
  have hA₀ : 0≤A := (Finset.sum_nonneg (fun k _ => abs_nonneg (a.coeff k))).trans hA
  have hB₀ : 0≤B := (Finset.sum_nonneg (fun k _ => abs_nonneg (b.coeff k))).trans hB
  have hT₀ : 0≤T := (abs_nonneg _).trans (hT 0 (by constructor <;> norm_num [cellDomain]))
  have hR : (0:ℝ)≤R.error :=
    (add_nonneg (add_nonneg (add_nonneg hT₀ (mul_nonneg he₁ hB₀))
      (mul_nonneg he₂ hA₀)) (mul_nonneg he₁ he₂)).trans he
  refine ⟨by exact_mod_cast hR, cauchyLow a.coeff b.coeff, hc, ?_⟩
  intro x hx
  have hPa := (scalarEval_abs_le_sum a.coeff x hx).trans hA
  have hPb := (scalarEval_abs_le_sum b.coeff x hx).trans hB
  have hdf := a.remainder x hx
  have hdg := b.remainder x hx
  have hsplit := scalarEval_product_split a.coeff b.coeff x
  have hid : f x*g x-scalarEval (cauchyLow a.coeff b.coeff) x =
      x^(n+1)*(cauchyHigh a.coeff b.coeff).eval x +
      (f x-scalarEval a.coeff x)*scalarEval b.coeff x +
      (g x-scalarEval b.coeff x)*scalarEval a.coeff x +
      (f x-scalarEval a.coeff x)*(g x-scalarEval b.coeff x) := by
    nlinarith only [hsplit]
  rw [hid]
  calc
    _ ≤ |x^(n+1)*(cauchyHigh a.coeff b.coeff).eval x| +
        |(f x-scalarEval a.coeff x)*scalarEval b.coeff x| +
        |(g x-scalarEval b.coeff x)*scalarEval a.coeff x| +
        |(f x-scalarEval a.coeff x)*(g x-scalarEval b.coeff x)| := abs_add_four_le _ _ _ _
    _ ≤ T+(M₁.error:ℝ)*B+(M₂.error:ℝ)*A+(M₁.error:ℝ)*(M₂.error:ℝ) := by
      simp only [abs_mul]
      exact add_le_add (add_le_add (add_le_add (by simpa only [abs_mul] using hT x hx)
        (mul_le_mul hdf hPb (abs_nonneg _) he₁))
        (mul_le_mul hdg hPa (abs_nonneg _) he₂))
        (mul_le_mul hdf hdg (abs_nonneg _) he₁)
    _ ≤ (R.error:ℝ) := he

#check scalar_models_product_error
#print ScalarProductErrorStatement
#print axioms scalar_models_product_error
end Blueprint.CAP
