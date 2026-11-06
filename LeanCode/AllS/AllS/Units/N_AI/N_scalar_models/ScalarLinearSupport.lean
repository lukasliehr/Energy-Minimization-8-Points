import AllS.Units.N_AI.N_data.ScalarLinearGates
import AllS.Units.N_AI.N_scalar_models.AffineModelSupport

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def ScalarLinearSupportStatement : Prop :=
  (∀ {n m : ℕ} (M : Fin m → QModel n) (q : Fin m → ℚ) (R : QModel n)
      (f : Fin m → ℝ → ℝ), (∀ i, (M i).asTM.Valid (f i)) →
      QModel.LinearCombinationGate M q R → R.asTM.Valid (fun x => ∑ i, (q i:ℝ)*f i x)) ∧
  (∀ {n : ℕ} (M R : QModel n) (I : QInterval) (μ : ℚ) (f : ℝ → ℝ) (c : ℝ),
      M.asTM.Valid f → I.asBox.Contains c → M.ConstantDivisionGate R I μ →
      R.asTM.Valid (fun x => f x/c))

theorem scalarEval_linearCombination {n m : ℕ} (q : Fin m → ℝ)
    (a : Fin m → Fin (n+1) → ℝ) (x : ℝ) :
    scalarEval (fun k => ∑ i, q i*a i k) x = ∑ i, q i*scalarEval (a i) x := by
  simp only [scalarEval,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  exact Finset.sum_comm

theorem QModel.linear_combination_valid {n m : ℕ} (M : Fin m → QModel n)
    (q : Fin m → ℚ) (R : QModel n) (f : Fin m → ℝ → ℝ)
    (hM : ∀ i, (M i).asTM.Valid (f i)) (hg : QModel.LinearCombinationGate M q R) :
    R.asTM.Valid (fun x => ∑ i, (q i:ℝ)*f i x) := by
  classical
  choose a ha hr using fun i => (hM i).2
  have he : 0 ≤ R.error :=
    (Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (hM i).1)).trans hg.2
  refine ⟨he,(fun k => ∑ i, (q i:ℝ)*a i k),?_,?_⟩
  · intro k
    exact QInterval.subset_contains
      (QInterval.sum_contains _ _ (fun i => QInterval.scale_contains (q i) (ha i k))) (hg.1 k)
  · intro x hx
    rw [scalarEval_linearCombination,←Finset.sum_sub_distrib]
    have hterm (i : Fin m) :
        |(q i:ℝ)*f i x-(q i:ℝ)*scalarEval (a i) x| ≤ |(q i:ℝ)| * ((M i).error:ℝ) := by
      rw [←mul_sub,abs_mul]
      exact mul_le_mul_of_nonneg_left (hr i x hx) (abs_nonneg _)
    exact ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun i _ => hterm i))).trans (by exact_mod_cast hg.2)

theorem scalarEval_div_constant {n : ℕ} (a : Fin (n+1) → ℝ) (c x : ℝ) :
    scalarEval (fun k => a k/c) x = scalarEval a x/c := by
  simpa only [div_eq_mul_inv,mul_comm] using scalarEval_scale c⁻¹ a x

theorem QModel.constant_division_valid {n : ℕ} (M R : QModel n) (I : QInterval)
    (μ : ℚ) (f : ℝ → ℝ) (c : ℝ) (hM : M.asTM.Valid f) (hc : I.asBox.Contains c)
    (hg : M.ConstantDivisionGate R I μ) : R.asTM.Valid (fun x => f x/c) := by
  have hμ : (0:ℝ) < μ := by exact_mod_cast hg.1
  have hside : 0 < I.lo ∨ I.hi < 0 := hg.2.1.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hsep : (μ:ℝ) ≤ |c| := by
    rcases hg.2.1 with hp | hn
    · have h : (μ:ℝ) ≤ I.lo := by exact_mod_cast hp.2
      exact h.trans (hc.1.trans (le_abs_self _))
    · have h : (μ:ℝ) ≤ -(I.hi:ℝ) := by exact_mod_cast hn.2
      exact h.trans ((neg_le_neg hc.2).trans (neg_le_abs _))
  obtain ⟨he,a,ha,hr⟩ := hM
  refine ⟨(div_nonneg he hg.1.le).trans hg.2.2.2,(fun k => a k/c),?_,?_⟩
  · intro k
    change (R.coeff k).asBox.Contains (a k/c)
    have h := QInterval.mul_contains (ha k) (QInterval.inv_contains hc hside)
    simpa only [one_div,div_eq_mul_inv,one_mul] using QInterval.subset_contains h (hg.2.2.1 k)
  · intro x hx
    rw [scalarEval_div_constant,←sub_div,abs_div]
    calc
      |f x-scalarEval a x|/|c| ≤ (M.error:ℝ)/|c| :=
        div_le_div_of_nonneg_right (hr x hx) (abs_nonneg c)
      _ ≤ (M.error:ℝ)/(μ:ℝ) :=
        div_le_div_of_nonneg_left (by exact_mod_cast he) hμ hsep
      _ ≤ (R.error:ℝ) := by exact_mod_cast hg.2.2.2

theorem scalarLinearSupport : ScalarLinearSupportStatement :=
  ⟨QModel.linear_combination_valid,QModel.constant_division_valid⟩
#print ScalarLinearSupportStatement
#print axioms scalarLinearSupport
end Blueprint.CAP
