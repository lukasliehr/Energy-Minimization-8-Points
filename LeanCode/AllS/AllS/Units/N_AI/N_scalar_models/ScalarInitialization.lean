import AllS.Units.N_AI.N_scalar_models.N_constant_reciprocal
import AllS.Units.N_AI.N_scalar_models.N_sum_error_widen

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def ScalarInitializationStatement : Prop :=
  (∀ {n : ℕ} (M : TM n) (a : Fin (n+1) → ℝ),
    M.CoeffContains a → 0 ≤ M.error → M.Valid (scalarEval a)) ∧
  (∀ {n : ℕ} (I : Box) (a : ℝ), I.Contains a →
    (TM.constantBox n I).Valid (fun _ => a)) ∧
  (∀ {n : ℕ} (M R : TM n) (f : ℝ → ℝ) (q : ℚ),
    M.Valid f → (∀ k, Box.ScaleGate q (M.coeff k) (R.coeff k)) →
    |q| * M.error ≤ R.error → R.Valid (fun x => (q:ℝ)*f x))

theorem TM.valid_polynomial {n : ℕ} (M : TM n) (a : Fin (n+1) → ℝ)
    (ha : M.CoeffContains a) (he : 0 ≤ M.error) : M.Valid (scalarEval a) := by
  refine ⟨he, a, ha, ?_⟩
  intro x hx
  simpa using (show (0:ℝ) ≤ M.error by exact_mod_cast he)

theorem TM.valid_const {n : ℕ} (I : Box) (a : ℝ) (ha : I.Contains a) :
    (TM.constantBox n I).Valid (fun _ => a) := by
  classical
  refine ⟨le_rfl, (fun k => if k = 0 then a else 0), ?_, ?_⟩
  · intro k
    by_cases hk : k = 0
    · simpa [TM.constantBox, hk] using ha
    · simp [TM.constantBox, hk, Box.Contains, Box.point]
  · intro x hx
    simp [scalarEval_single_zero, TM.constantBox]

theorem scalarEval_scale {n : ℕ} (q : ℝ) (a : Fin (n+1) → ℝ) (x : ℝ) :
    scalarEval (fun k => q * a k) x = q * scalarEval a x := by
  simp [scalarEval, Finset.mul_sum, mul_assoc]

theorem TM.valid_scale {n : ℕ} (M R : TM n) (f : ℝ → ℝ) (q : ℚ)
    (hm : M.Valid f) (hc : ∀ k, Box.ScaleGate q (M.coeff k) (R.coeff k))
    (he : |q| * M.error ≤ R.error) : R.Valid (fun x => (q:ℝ) * f x) := by
  rcases hm with ⟨hem, a, ha, hr⟩
  refine ⟨(mul_nonneg (abs_nonneg q) hem).trans he, (fun k => (q:ℝ) * a k), ?_, ?_⟩
  · exact fun k => Box.contains_scale (ha k) (hc k)
  · intro x hx
    rw [scalarEval_scale, ←mul_sub, abs_mul]
    exact (mul_le_mul_of_nonneg_left (hr x hx) (abs_nonneg (q:ℝ))).trans
      (by exact_mod_cast he)

theorem TM.valid_congr_on {n : ℕ} (M : TM n) (f g : ℝ → ℝ)
    (hm : M.Valid f) (hfg : ∀ x ∈ cellDomain, f x = g x) : M.Valid g := by
  rcases hm with ⟨he, a, ha, hr⟩
  exact ⟨he, a, ha, fun x hx => by simpa only [←hfg x hx] using hr x hx⟩

theorem scalar_initialization : ScalarInitializationStatement :=
  ⟨TM.valid_polynomial, TM.valid_const, TM.valid_scale⟩

#check scalar_initialization
#print ScalarInitializationStatement
#print axioms scalar_initialization
#print axioms TM.valid_congr_on
end Blueprint.CAP
