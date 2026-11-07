import AllS.Units.N_AI.N_data.StructuredResidualGates
import AllS.Units.N_AI.N_scalar_models.ScalarLinearSupport

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

/-- One error function per Hermite coefficient is shared by all coordinates. -/
def StructuredResidualWitness {n t r : ℕ} (H : Fin t → QModel n)
    (q : Fin r → Fin t → ℚ) (R : Fin r → QModel n)
    (f : Fin r → ℝ → ℝ) : Prop :=
  ∃ (a : Fin r → Fin (n+1) → ℝ) (e : Fin t → ℝ → ℝ)
    (ε : Fin r → ℝ → ℝ),
    (∀ i k, ((R i).coeff k).asBox.Contains (a i k)) ∧
    (∀ j x, x ∈ cellDomain → |e j x| ≤ ((H j).error:ℝ)) ∧
    (∀ i x, x ∈ cellDomain → |ε i x| ≤ ((R i).error:ℝ)) ∧
    ∀ i x, f i x=scalarEval (a i) x+(∑ j,(q i j:ℝ)*e j x)+ε i x

theorem structuredResidualSupport {n t b r : ℕ} (H : Fin t → QModel n)
    (B : Fin b → Fin r → QModel n) (q : Fin r → Fin t → ℚ)
    (R : Fin r → QModel n) (h : Fin t → ℝ → ℝ)
    (g : Fin b → Fin r → ℝ → ℝ)
    (hH : ∀ j, (H j).asTM.Valid (h j))
    (hB : ∀ j i, (B j i).asTM.Valid (g j i))
    (hg : StructuredResidualGate H B q R) :
    StructuredResidualWitness H q R (fun i x => ∑ j,(q i j:ℝ)*h j x-∑ j,g j i x) := by
  classical
  choose a ha he using fun j => (hH j).2
  choose c hc ce using fun j i => (hB j i).2
  let d : Fin r → Fin (n+1) → ℝ := fun i k =>
    (∑ j,(q i j:ℝ)*a j k)-(∑ j,c j i k)
  refine ⟨d,(fun j x => h j x-scalarEval (a j) x),
    (fun i x => -(∑ j,(g j i x-scalarEval (c j i) x))),?_,he,?_,?_⟩
  · intro i k
    have hh := QInterval.sum_contains _ _ (fun j => QInterval.scale_contains (q i j) (ha j k))
    have hb := QInterval.sum_contains _ _ (fun j => QInterval.neg_contains (hc j i k))
    have hh' := QInterval.subset_contains (QInterval.add_contains hh hb) (hg.1 i k)
    simpa only [d,Finset.sum_neg_distrib,sub_eq_add_neg] using hh'
  · intro i x hx
    rw [abs_neg]
    apply ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun j _ => ce j i x hx)).trans
    exact_mod_cast hg.2 i
  · intro i x
    have hd : scalarEval (d i) x=
        (∑ j,(q i j:ℝ)*scalarEval (a j) x)-(∑ j,scalarEval (c j i) x) := by
      unfold scalarEval d
      simp only [sub_mul,Finset.sum_sub_distrib,Finset.sum_mul,Finset.mul_sum,mul_assoc]
      congr 1 <;> exact Finset.sum_comm
    rw [hd]
    simp only [mul_sub,Finset.sum_sub_distrib]
    ring

#print axioms structuredResidualSupport
end Blueprint.CAP
