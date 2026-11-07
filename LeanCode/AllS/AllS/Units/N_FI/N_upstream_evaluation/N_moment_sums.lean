import AllS.Units.N_FI.N_upstream_evaluation.N_S_R_eval

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

def polyOnTriples (Y : Configuration) (p : Poly3) (i j k : Fin 8) : ℝ :=
  MvPolynomial.eval ![inner ℝ (Y i) (Y j),inner ℝ (Y i) (Y k),inner ℝ (Y j) (Y k)] p

def allPolySum (Y : Configuration) (p : Poly3) : ℝ :=
  ∑ i : Fin 8, ∑ j : Fin 8, ∑ k : Fin 8, polyOnTriples Y p i j k

def distinctPolySum (Y : Configuration) (p : Poly3) : ℝ :=
  DistinctSum (polyOnTriples Y p)

def canonicalMoment (m k : ℕ) (Y : Configuration) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => allPolySum Y (kernelSPoly k i.val j.val)

def MomentEvaluationContract : Prop :=
  (∀ m k : ℕ, ∀ Y : Configuration, canonicalMoment m k Y = GenericMoments.momentMatrix m k Y) ∧
  (∀ Y : Configuration, ∀ p : Poly3,
    allPolySum Y p = GenericMoments.tripleSum
      (GenericMoments.onTriples Y (fun u v t => MvPolynomial.eval ![u,v,t] p)) ∧
    distinctPolySum Y p = GenericMoments.distinctSum
      (GenericMoments.onTriples Y (fun u v t => MvPolynomial.eval ![u,v,t] p)))

theorem canonicalMoment_eq_generic (m k : ℕ) (Y : Configuration) :
    canonicalMoment m k Y = GenericMoments.momentMatrix m k Y := by
  ext i j
  rw [GenericMoments.momentMatrix_eq_sum_Sfun]
  simp [canonicalMoment,allPolySum,polyOnTriples,GenericMoments.tripleSum,
    GenericMoments.onTriples,kernelSPoly_eval]

theorem upstream_evaluation_moment_sums : MomentEvaluationContract := by
  refine ⟨canonicalMoment_eq_generic, ?_⟩
  intro Y p
  exact ⟨rfl,rfl⟩

#check upstream_evaluation_moment_sums
#print axioms upstream_evaluation_moment_sums
#check MomentEvaluationContract
#print axioms MomentEvaluationContract
end Blueprint.Thomson.Finite
