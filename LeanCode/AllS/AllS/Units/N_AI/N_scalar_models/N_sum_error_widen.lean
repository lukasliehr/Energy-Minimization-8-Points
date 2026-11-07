import Blueprint.CAPContracts
import AllS.Units.N_AI.N_interval_semantics.N_affine
import Blueprint.Target

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP
def ScalarSumErrorWidenStatement : Prop :=
  (∀ {n : ℕ} (M₁ M₂ R : TM n) (f g : ℝ→ℝ), M₁.Valid f → M₂.Valid g →
    (∀ k, Box.AddGate (M₁.coeff k) (M₂.coeff k) (R.coeff k)) →
    M₁.error+M₂.error≤R.error → R.Valid (fun x=>f x+g x)) ∧
  (∀ {n : ℕ} (M R : TM n) (f : ℝ→ℝ), M.Valid f →
    (∀ k, Box.NegGate (M.coeff k) (R.coeff k)) → M.error≤R.error →
    R.Valid (fun x=> -f x)) ∧
  (∀ {n : ℕ} (M R : TM n) (f : ℝ→ℝ), M.Valid f →
    R.coeff=M.coeff → M.error≤R.error → R.Valid f)
theorem scalarEval_add {n : ℕ} (a b : Fin (n+1)→ℝ) (x : ℝ) :
    scalarEval (fun k=>a k+b k) x = scalarEval a x+scalarEval b x := by
  simp [scalarEval, add_mul, Finset.sum_add_distrib]

theorem scalarEval_neg {n : ℕ} (a : Fin (n+1)→ℝ) (x : ℝ) :
    scalarEval (fun k=> -a k) x = -scalarEval a x := by
  simp [scalarEval, Finset.sum_neg_distrib]

theorem TM.valid_add {n : ℕ} (M₁ M₂ R : TM n) (f g : ℝ→ℝ)
    (h₁ : M₁.Valid f) (h₂ : M₂.Valid g)
    (hc : ∀ k, Box.AddGate (M₁.coeff k) (M₂.coeff k) (R.coeff k))
    (he : M₁.error+M₂.error≤R.error) : R.Valid (fun x=>f x+g x) := by
  rcases h₁ with ⟨he₁,a,ha,hr₁⟩
  rcases h₂ with ⟨he₂,b,hb,hr₂⟩
  refine ⟨(add_nonneg he₁ he₂).trans he, (fun k=>a k+b k), ?_, ?_⟩
  · exact fun k => Box.contains_add (ha k) (hb k) (hc k)
  · intro x hx
    calc
      |f x+g x-scalarEval (fun k=>a k+b k) x| =
          |(f x-scalarEval a x)+(g x-scalarEval b x)| := by
            rw [scalarEval_add]
            congr 1
            ring
      _ ≤ |f x-scalarEval a x|+|g x-scalarEval b x| := abs_add_le _ _
      _ ≤ (M₁.error:ℝ)+(M₂.error:ℝ) := add_le_add (hr₁ x hx) (hr₂ x hx)
      _ ≤ (R.error:ℝ) := by exact_mod_cast he

theorem TM.valid_neg {n : ℕ} (M R : TM n) (f : ℝ→ℝ)
    (hm : M.Valid f) (hc : ∀ k, Box.NegGate (M.coeff k) (R.coeff k))
    (he : M.error≤R.error) : R.Valid (fun x=> -f x) := by
  rcases hm with ⟨hem,a,ha,hr⟩
  refine ⟨hem.trans he, (fun k=> -a k), ?_, ?_⟩
  · exact fun k => Box.contains_neg (ha k) (hc k)
  · intro x hx
    calc
      |-f x-scalarEval (fun k=> -a k) x| = |-(f x-scalarEval a x)| := by
        rw [scalarEval_neg]
        congr 1
        ring
      _ = |f x-scalarEval a x| := abs_neg _
      _ ≤ (M.error:ℝ) := hr x hx
      _ ≤ (R.error:ℝ) := by exact_mod_cast he

theorem TM.valid_error_widen {n : ℕ} (M R : TM n) (f : ℝ→ℝ)
    (hm : M.Valid f) (hc : R.coeff=M.coeff) (he : M.error≤R.error) : R.Valid f := by
  rcases hm with ⟨hem,a,ha,hr⟩
  refine ⟨hem.trans he, a, ?_, ?_⟩
  · simpa only [TM.CoeffContains, hc] using ha
  · intro x hx
    exact (hr x hx).trans (by exact_mod_cast he)

theorem scalar_models_sum_error_widen : ScalarSumErrorWidenStatement :=
  ⟨TM.valid_add, TM.valid_neg, TM.valid_error_widen⟩
#check scalar_models_sum_error_widen
#print ScalarSumErrorWidenStatement
#print axioms scalar_models_sum_error_widen
end Blueprint.CAP
