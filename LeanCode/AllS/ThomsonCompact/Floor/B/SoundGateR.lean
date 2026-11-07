import AllS.Units.N_AI.N_data.StructuredResidualGates
import AllS.Units.N_AI.N_data.StructuredCenterGates

/-!
# Residual gate by construction (F3b)

For any target models `H`, contribution models `B` (e.g. F2's `w0Part4.B`, `nb = 112`) and directions `q`, the
residual models `gateR H B q` (the gate's own interval combination, error `Σ_b B.error`) satisfy
`StructuredResidualGate` with no check at all (`gateR_gate`). For point models (packed TMs through `toQModel`)
the residual coefficients are points (`gateR_point`), so the centre gate is an exact rational inequality
(`centre_of_points`).
-/

namespace ThomsonCompact.Floor.B
open Blueprint.CAP
open scoped BigOperators

/-- the residual models by construction -/
def gateR {n t b r : ℕ} (H : Fin t → QModel n) (B : Fin b → Fin r → QModel n) (q : Fin r → Fin t → ℚ) :
    Fin r → QModel n :=
  fun i => ⟨fun k => (QInterval.sum fun j => (H j |>.coeff k).scale (q i j)).add
      (QInterval.sum fun j => (B j i |>.coeff k).neg), ∑ j, (B j i).error⟩

/-- **`Residual12.gate` for any `H`, `B`, `q`** (with `Rm := gateR H B q`). -/
theorem gateR_gate {n t b r : ℕ} (H : Fin t → QModel n) (B : Fin b → Fin r → QModel n) (q : Fin r → Fin t → ℚ) :
    StructuredResidualGate H B q (gateR H B q) :=
  ⟨fun _ _ => ⟨le_rfl, le_rfl⟩, fun _ => le_rfl⟩

/-- point models give point residual coefficients -/
theorem gateR_point {n t b r : ℕ} (H : Fin t → QModel n) (B : Fin b → Fin r → QModel n) (q : Fin r → Fin t → ℚ)
    (h : Fin t → Fin (n + 1) → ℚ) (β : Fin b → Fin r → Fin (n + 1) → ℚ)
    (hH : ∀ j k, (H j).coeff k = ⟨h j k, h j k⟩) (hB : ∀ j i k, (B j i).coeff k = ⟨β j i k, β j i k⟩)
    (i : Fin r) (k : Fin (n + 1)) :
    ((gateR H B q i).coeff k).lo = ∑ j, q i j * h j k - ∑ j, β j i k ∧
    ((gateR H B q i).coeff k).hi = ∑ j, q i j * h j k - ∑ j, β j i k := by
  simp only [gateR, QInterval.add, QInterval.sum, QInterval.scale, QInterval.neg, hH, hB, min_self, max_self,
    Finset.sum_neg_distrib]
  exact ⟨(sub_eq_add_neg _ _).symm, (sub_eq_add_neg _ _).symm⟩

/-- **The centre gate for point models** reduces to one exact inequality per coordinate. -/
theorem centre_of_points {n t b r : ℕ} (H : Fin t → QModel n) (B : Fin b → Fin r → QModel n)
    (q : Fin r → Fin t → ℚ) (h : Fin t → Fin (n + 1) → ℚ) (β : Fin b → Fin r → Fin (n + 1) → ℚ)
    (hH : ∀ j k, (H j).coeff k = ⟨h j k, h j k⟩) (hB : ∀ j i k, (B j i).coeff k = ⟨β j i k, β j i k⟩)
    (c : Fin r → Fin (n + 1) → ℚ) (E : Fin r → ℚ)
    (hE : ∀ i, (∑ k, |∑ j, q i j * h j k - ∑ j, β j i k - c i k|) + ∑ j, (B j i).error ≤ E i) :
    StructuredCenterGate (gateR H B q) c E := by
  intro i
  have e : ∀ k, max |((gateR H B q i).coeff k).lo - c i k| |((gateR H B q i).coeff k).hi - c i k| =
      |∑ j, q i j * h j k - ∑ j, β j i k - c i k| := by
    intro k
    rw [(gateR_point H B q h β hH hB i k).1, (gateR_point H B q h β hH hB i k).2, max_self]
  simp only [e]
  exact hE i

end ThomsonCompact.Floor.B
