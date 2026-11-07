import AllS.Units.N_AI.N_data.MatrixScalarGates
import AllS.Units.N_AI.N_scalar_models.IntervalExpressionSupport

noncomputable section
namespace Blueprint.CAP

def QMatrixModel.asMatrixTM {N m n : ℕ} (M : QMatrixModel N m n) : MatrixTM N m n :=
  ⟨fun k i j => (M.coeff k i j).asBox,M.error⟩

def ScalarMatrixSupportStatement : Prop :=
  ∀ {N m n : ℕ} (S : Fin m → Fin n → QModel N) (R : QMatrixModel N m n)
    (f : ℝ → Matrix (Fin m) (Fin n) ℝ),
    (∀ i j, (S i j).asTM.Valid (fun x => f x i j)) →
    R.FromScalarsGate S → R.asMatrixTM.Valid f

theorem scalarMatrixSupport : ScalarMatrixSupportStatement := by
  intro N m n S R f hS hg
  change (∀ i j, 0 ≤ (S i j).asTM.error ∧ ∃ a,
    (S i j).asTM.CoeffContains a ∧
    ∀ x ∈ cellDomain, |f x i j-scalarEval a x| ≤ ((S i j).asTM.error:ℝ)) at hS
  choose he a ha hr using hS
  refine ⟨fun i j => (he i j).trans (hg.2 i j), (fun k i j => a i j k), ?_, ?_⟩
  · intro k i j
    exact QInterval.subset_contains (ha i j k) (hg.1 k i j)
  · intro x hx i j
    exact (hr i j x hx).trans (by exact_mod_cast hg.2 i j)

theorem MatrixTM.valid_congr_on {N m n : ℕ} (M : MatrixTM N m n)
    (f g : ℝ → Matrix (Fin m) (Fin n) ℝ) (hf : M.Valid f)
    (hfg : ∀ x ∈ cellDomain, f x = g x) : M.Valid g := by
  rcases hf with ⟨he,a,ha,hr⟩
  exact ⟨he,a,ha,fun x hx i j => by rw [← hfg x hx]; exact hr x hx i j⟩

#print ScalarMatrixSupportStatement
#print axioms scalarMatrixSupport
#print axioms MatrixTM.valid_congr_on
end Blueprint.CAP
