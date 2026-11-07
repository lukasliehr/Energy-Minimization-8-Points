import AllS.Units.N_AI.N_data.AffineModelGates
import AllS.Units.N_AI.N_scalar_models.IntervalExpressionSupport
import AllS.Units.N_AI.N_scalar_models.ScalarInitialization

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def AffineModelSupportStatement : Prop :=
  (∀ {n : ℕ} (M : QModel (n+1)) (c h : ℚ), M.AffineGate c h →
    M.asTM.Valid (fun x => (c:ℝ)+(h:ℝ)*x)) ∧
  (∀ {n : ℕ} (M : QModel n) (I : QInterval) (a : ℝ), M.ConstGate I →
    I.asBox.Contains a → M.asTM.Valid (fun _ => a)) ∧
  (∀ {n : ℕ} (A B R : QModel n) (f g : ℝ → ℝ), A.asTM.Valid f → B.asTM.Valid g →
    A.AddGate B R → R.asTM.Valid (fun x => f x+g x)) ∧
  (∀ {n : ℕ} (A R : QModel n) (f : ℝ → ℝ), A.asTM.Valid f → A.NegGate R →
    R.asTM.Valid (fun x => -f x)) ∧
  (∀ {n : ℕ} (A R : QModel n) (f : ℝ → ℝ) (q : ℚ), A.asTM.Valid f → A.ScaleGate R q →
    R.asTM.Valid (fun x => (q:ℝ)*f x))

theorem qAffineCoefficients_eval (n : ℕ) (c h : ℚ) (x : ℝ) :
    scalarEval (fun k => (qAffineCoefficients n c h k:ℝ)) x = (c:ℝ)+(h:ℝ)*x := by
  simp [scalarEval, qAffineCoefficients, Fin.sum_univ_succ]

theorem QModel.point_polynomial_valid {n : ℕ} (a : Fin (n+1) → ℚ) :
    (QModel.pointPolynomial a).asTM.Valid (scalarEval (fun k => (a k:ℝ))) := by
  exact TM.pointPolynomial_valid a

theorem QModel.affine_gate_valid {n : ℕ} (M : QModel (n+1)) (c h : ℚ)
    (hg : M.AffineGate c h) : M.asTM.Valid (fun x => (c:ℝ)+(h:ℝ)*x) := by
  have hc : M.asTM.CoeffContains (fun k => (qAffineCoefficients n c h k:ℝ)) := by
    intro k
    change ((M.coeff k).lo:ℝ) ≤ (qAffineCoefficients n c h k:ℝ) ∧
      (qAffineCoefficients n c h k:ℝ) ≤ ((M.coeff k).hi:ℝ)
    constructor
    · exact_mod_cast (hg.1 k).1
    · exact_mod_cast (hg.1 k).2
  exact TM.valid_congr_on M.asTM _ _ (TM.valid_polynomial M.asTM _ hc hg.2)
    (fun x _ => qAffineCoefficients_eval n c h x)

theorem QModel.const_gate_valid {n : ℕ} (M : QModel n) (I : QInterval) (a : ℝ)
    (hg : M.ConstGate I) (ha : I.asBox.Contains a) : M.asTM.Valid (fun _ => a) := by
  classical
  let c : Fin (n+1) → ℝ := fun k => if k=0 then a else 0
  have hc : M.asTM.CoeffContains c := by
    intro k
    by_cases hk : k=0
    · subst k
      exact QInterval.subset_contains ha hg.1
    · change (M.coeff k).asBox.Contains (if k=0 then a else 0)
      rw [if_neg hk]
      constructor
      · exact_mod_cast (hg.2.1 k hk).1
      · exact_mod_cast (hg.2.1 k hk).2
  exact TM.valid_congr_on M.asTM _ _ (TM.valid_polynomial M.asTM c hc hg.2.2)
    (fun x _ => scalarEval_single_zero a x)

theorem QModel.add_gate_valid {n : ℕ} (A B R : QModel n) (f g : ℝ → ℝ)
    (ha : A.asTM.Valid f) (hb : B.asTM.Valid g) (hg : A.AddGate B R) :
    R.asTM.Valid (fun x => f x+g x) := by
  apply TM.valid_add A.asTM B.asTM R.asTM f g ha hb _ hg.2
  intro k
  exact ⟨(hg.1 k).1,(hg.1 k).2⟩

theorem QModel.neg_gate_valid {n : ℕ} (A R : QModel n) (f : ℝ → ℝ)
    (ha : A.asTM.Valid f) (hg : A.NegGate R) : R.asTM.Valid (fun x => -f x) := by
  apply TM.valid_neg A.asTM R.asTM f ha _ hg.2
  intro k
  exact ⟨(hg.1 k).1,(hg.1 k).2⟩

theorem QModel.scale_gate_valid {n : ℕ} (A R : QModel n) (f : ℝ → ℝ) (q : ℚ)
    (ha : A.asTM.Valid f) (hg : A.ScaleGate R q) : R.asTM.Valid (fun x => (q:ℝ)*f x) := by
  apply TM.valid_scale A.asTM R.asTM f q ha _ hg.2
  intro k
  rcases le_total 0 q with hq | hq
  · exact Or.inl ⟨hq,(hg.1 k).1.trans (min_le_left _ _),
      (le_max_right _ _).trans (hg.1 k).2⟩
  · exact Or.inr ⟨hq,(hg.1 k).1.trans (min_le_right _ _),
      (le_max_left _ _).trans (hg.1 k).2⟩

theorem affineModelSupport : AffineModelSupportStatement :=
  ⟨QModel.affine_gate_valid,QModel.const_gate_valid,QModel.add_gate_valid,
    QModel.neg_gate_valid,QModel.scale_gate_valid⟩

#check affineModelSupport
#print AffineModelSupportStatement
#print axioms affineModelSupport
#print axioms QModel.point_polynomial_valid
end Blueprint.CAP
