import ThomsonCompact.CoeffMap.RFCodec
import ThomsonCompact.Packed.ListPoly
import Blueprint.CAPContracts

/-!
# Packed rational-function kernel columns: generic part (F2a)

A kernel-column coefficient is a rational function of the height `a`. The old catalogue stores it as
`RatFun ⟨P, 0, Q⟩` with Mathlib `Polynomial ℚ` literals `C q₀ * X^0 + C q₁ * X^1 + …` (all D12 columns have
zero `√2` part and dense literals). The compact form is an `RFRec`: integer coefficient lists `num`, `den`
and scales with `P = Σ (numₖ / scaleN) Xᵏ`, `Q = Σ (denₖ / scaleD) Xᵏ`; its value is
`(evalZ num a / scaleN) / (evalZ den a / scaleD)` (`evalZ` is the F1 list evaluation, so F1's rational
evaluation at a height TM applies directly).

* decoding (`slots`, `numOfSlots`, `denOfSlots`, `tableRec`) is in the Init-only `RFCodec`.
* `RFRec.toRatFun`: the old-catalogue literal shape; `RFRec.eval_toRatFun`, `RFRec.definedAt_iff`: its
  semantics. The bridge to an old constant `rfNNNN` is then `rfNNNN = (rec k).toRatFun` by `rfl`.
-/

namespace ThomsonCompact.CoeffMap

open Blueprint.CAP ThomsonCompact.Packed

/-! ## The old literal shape and its semantics -/

/-- `acc + C q₀ X^k + C q₁ X^(k+1) + …`, associated to the left like the catalogue literals. -/
noncomputable def polyGo : List ℚ → ℕ → Polynomial ℚ → Polynomial ℚ
  | [], _, acc => acc
  | q :: L, k, acc => polyGo L (k + 1) (acc + Polynomial.C q * Polynomial.X ^ k)

/-- `C q₀ * X^0 + C q₁ * X^1 + …` (and `0` for the empty list), the exact catalogue literal shape. -/
noncomputable def polyOfCoeffs : List ℚ → Polynomial ℚ
  | [] => 0
  | q :: L => polyGo L 1 (Polynomial.C q * Polynomial.X ^ 0)

/-- The old-catalogue `RatFun` of a record. -/
noncomputable def RFRec.toRatFun (r : RFRec) : RatFun :=
  ⟨polyOfCoeffs (r.num.map fun n : ℤ => (n : ℚ) / (r.scaleN : ℚ)), 0,
    polyOfCoeffs (r.den.map fun n : ℤ => (n : ℚ) / (r.scaleD : ℚ))⟩

/-- Real value of a record. -/
noncomputable def RFRec.value (r : RFRec) (a : ℝ) : ℝ :=
  (evalZ r.num a / r.scaleN) / (evalZ r.den a / r.scaleD)

/-- `Σ qᵢ a^(k+i)`. -/
noncomputable def qFrom : List ℚ → ℕ → ℝ → ℝ
  | [], _, _ => 0
  | q :: L, k, a => (q : ℝ) * a ^ k + qFrom L (k + 1) a

theorem evalQPoly_add (p q : Polynomial ℚ) (a : ℝ) : evalQPoly (p + q) a = evalQPoly p a + evalQPoly q a := by
  simp [evalQPoly]

theorem evalQPoly_monomial (q : ℚ) (k : ℕ) (a : ℝ) :
    evalQPoly (Polynomial.C q * Polynomial.X ^ k) a = (q : ℝ) * a ^ k := by
  simp [evalQPoly]

theorem evalQPoly_polyGo : ∀ (L : List ℚ) (k : ℕ) (acc : Polynomial ℚ) (a : ℝ),
    evalQPoly (polyGo L k acc) a = evalQPoly acc a + qFrom L k a
  | [], _, acc, a => by simp [polyGo, qFrom]
  | q :: L, k, acc, a => by
    rw [polyGo, evalQPoly_polyGo L (k + 1), evalQPoly_add, evalQPoly_monomial, qFrom]
    ring

theorem qFrom_succ : ∀ (L : List ℚ) (k : ℕ) (a : ℝ), qFrom L (k + 1) a = a * qFrom L k a
  | [], _, _ => by simp [qFrom]
  | q :: L, k, a => by
    rw [qFrom, qFrom, qFrom_succ L (k + 1), pow_succ]
    ring

theorem qFrom_zero : ∀ (L : List ℚ) (a : ℝ), qFrom L 0 a = horner a (L.map (Rat.cast : ℚ → ℝ))
  | [], _ => by simp [qFrom]
  | q :: L, a => by
    rw [qFrom, qFrom_succ, qFrom_zero L a, List.map_cons, horner]
    ring

theorem evalQPoly_polyOfCoeffs (L : List ℚ) (a : ℝ) :
    evalQPoly (polyOfCoeffs L) a = horner a (L.map (Rat.cast : ℚ → ℝ)) := by
  cases L with
  | nil => simp [polyOfCoeffs, evalQPoly]
  | cons q L =>
    have h1 : qFrom L 1 a = a * qFrom L 0 a := qFrom_succ L 0 a
    rw [polyOfCoeffs, evalQPoly_polyGo, evalQPoly_monomial, h1, qFrom_zero, List.map_cons, horner]
    ring

theorem horner_scaled (D : ℕ) (a : ℝ) : ∀ L : List ℤ,
    horner a ((L.map fun n : ℤ => (n : ℚ) / (D : ℚ)).map (Rat.cast : ℚ → ℝ)) = evalZ L a / D
  | [] => by simp [evalZ]
  | n :: L => by
    have h := horner_scaled D a L
    simp only [evalZ, List.map_cons, horner] at h ⊢
    rw [h]
    push_cast
    ring

theorem evalQPoly_scaled (L : List ℤ) (D : ℕ) (a : ℝ) :
    evalQPoly (polyOfCoeffs (L.map fun n : ℤ => (n : ℚ) / (D : ℚ))) a = evalZ L a / D := by
  rw [evalQPoly_polyOfCoeffs, horner_scaled]

/-- **Semantics of a record in the old form**: `RatFun.eval` is the scaled integer-list quotient. -/
theorem RFRec.eval_toRatFun (r : RFRec) (a : ℝ) : r.toRatFun.eval a = r.value a := by
  have h0 : evalQPoly (0 : Polynomial ℚ) a = 0 := by simp [evalQPoly]
  simp only [RatFun.eval, RFRec.toRatFun, evalQPoly_scaled, RFRec.value, h0, mul_zero, add_zero]

theorem RFRec.definedAt_iff (r : RFRec) (a : ℝ) :
    r.toRatFun.DefinedAt a ↔ evalZ r.den a / r.scaleD ≠ 0 := by
  simp only [RatFun.DefinedAt, RFRec.toRatFun, evalQPoly_scaled]

#print axioms RFRec.eval_toRatFun
#print axioms RFRec.definedAt_iff

end ThomsonCompact.CoeffMap
