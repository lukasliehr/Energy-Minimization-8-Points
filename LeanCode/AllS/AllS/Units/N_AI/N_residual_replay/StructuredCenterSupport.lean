import AllS.Units.N_AI.N_residual_replay.StructuredResidualSupport
import AllS.Units.N_AI.N_data.StructuredCenterGates

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

theorem structuredCenterSupport {n t r : ℕ} (H : Fin t → QModel n)
    (q : Fin r → Fin t → ℚ) (R : Fin r → QModel n)
    (f : Fin r → ℝ → ℝ) (c : Fin r → Fin (n+1) → ℚ) (E : Fin r → ℚ)
    (hw : StructuredResidualWitness H q R f) (hg : StructuredCenterGate R c E) :
    ∃ (e : Fin t → ℝ → ℝ) (ε : Fin r → ℝ → ℝ),
      (∀ j x, x ∈ cellDomain → |e j x| ≤ ((H j).error:ℝ)) ∧
      (∀ i x, x ∈ cellDomain → |ε i x| ≤ (E i:ℝ)) ∧
      ∀ i x, f i x=scalarEval (fun k => (c i k:ℝ)) x+
        (∑ j,(q i j:ℝ)*e j x)+ε i x := by
  classical
  rcases hw with ⟨a,e,ε,ha,he,hε,hf⟩
  let d : Fin r → Fin (n+1) → ℝ := fun i k => a i k-(c i k:ℝ)
  have hd (i : Fin r) (k : Fin (n+1)) : |d i k| ≤
      ((max |((R i).coeff k).lo-c i k| |((R i).coeff k).hi-c i k|:ℚ):ℝ) := by
    have hb := Box.abs_le_magnitude (QInterval.add_contains (ha i k)
      (QInterval.point_contains (-c i k)))
    simpa [d,QInterval.asBox,QInterval.add,QInterval.point,Box.magnitude,sub_eq_add_neg] using hb
  refine ⟨e,(fun i x => scalarEval (d i) x+ε i x),he,?_,?_⟩
  · intro i x hx
    have hp := (scalarEval_abs_le_sum (d i) x hx).trans
      (Finset.sum_le_sum fun k _ => hd i k)
    have hb := (abs_add_le (scalarEval (d i) x) (ε i x)).trans (add_le_add hp (hε i x hx))
    exact hb.trans (by exact_mod_cast hg i)
  · intro i x
    rw [hf]
    have hs : scalarEval (a i) x=scalarEval (fun k => (c i k:ℝ)) x+scalarEval (d i) x := by
      simp only [scalarEval,d,sub_mul,Finset.sum_sub_distrib]
      ring
    rw [hs]
    ring

#print axioms structuredCenterSupport
end Blueprint.CAP
