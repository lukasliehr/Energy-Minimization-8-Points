import AllS.Units.N_AI.N_data.IntervalMatrixGates
import AllS.Units.N_AI.N_scalar_models.IntervalExpressionSupport
import AllS.Units.N_AI.N_correction_bounds.N_symmetric_majorant

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def QMatrixContains {m n : ℕ} (A : Matrix (Fin m) (Fin n) QInterval)
    (a : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ i j, (A i j).asBox.Contains (a i j)

theorem matrixProductIntervalSupport {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) QInterval)
    (B : Matrix (Fin n) (Fin p) QInterval)
    (C : Matrix (Fin m) (Fin p) QInterval)
    (a : Matrix (Fin m) (Fin n) ℝ) (b : Matrix (Fin n) (Fin p) ℝ)
    (ha : QMatrixContains A a) (hb : QMatrixContains B b)
    (hg : QMatrixProductGate A B C) : QMatrixContains C (a * b) := by
  intro i j
  exact QInterval.subset_contains
    (QInterval.sum_contains _ _ (fun h => QInterval.mul_contains (ha i h) (hb h j)))
    (hg i j)

theorem matrixCongruenceIntervalSupport {m n : ℕ}
    (Z : Matrix (Fin m) (Fin n) QInterval)
    (E : Matrix (Fin n) (Fin n) QInterval)
    (T : Matrix (Fin m) (Fin n) QInterval)
    (C : Matrix (Fin m) (Fin m) QInterval)
    (z : Matrix (Fin m) (Fin n) ℝ) (e : Matrix (Fin n) (Fin n) ℝ)
    (hz : QMatrixContains Z z) (he : QMatrixContains E e)
    (hleft : QMatrixProductGate Z E T) (hright : QMatrixProductGate T Z.transpose C) :
    QMatrixContains C (z * e * z.transpose) :=
  matrixProductIntervalSupport T Z.transpose C (z * e) z.transpose
    (matrixProductIntervalSupport Z E T z e hz he hleft) (fun i j => hz j i) hright

theorem weightedIntervalQuadraticSupport {n : ℕ}
    (C : Matrix (Fin n) (Fin n) QInterval)
    (M : Matrix (Fin n) (Fin n) ℚ) (w : Fin n → ℚ) (γ : ℚ)
    (E : Matrix (Fin n) (Fin n) ℝ)
    (hE : ∀ i j, E i j = E j i) (he : QMatrixContains C E)
    (hg : WeightedMajorantGate C M w γ) : QuadraticBound E (γ : ℝ) := by
  obtain ⟨hmajor, hsym, hnonneg, hw, hγ, hrow⟩ := hg
  have hmag : ∀ i j, |E i j| ≤ ((C i j).mag : ℝ) := by
    intro i j
    simpa only [Box.magnitude, QInterval.mag, QInterval.asBox] using
      Box.abs_le_magnitude (he i j)
  have hmin := (correction_bounds_symmetric_majorant E
    (fun i j => ((C i j).mag : ℝ)) hE hmag).1
  apply correction_bounds_weighted_quadratic E (fun i j => (M i j : ℝ))
    (fun i => (w i : ℝ)) (γ : ℝ) hE
  · intro i j
    exact_mod_cast hsym i j
  · intro i j
    exact_mod_cast hnonneg i j
  · intro i j
    apply (hmin i j).trans
    exact_mod_cast hmajor i j
  · intro i
    exact_mod_cast hw i
  · exact_mod_cast hγ
  · intro i
    exact_mod_cast hrow i

#print axioms matrixProductIntervalSupport
#print axioms matrixCongruenceIntervalSupport
#print axioms weightedIntervalQuadraticSupport
end Blueprint.CAP
