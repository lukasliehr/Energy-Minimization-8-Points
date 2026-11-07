import ThomsonCompact.Floor.B.SoundBridge
import AllS.Units.N_AI.N_fixed_tables.LinearSupport

/-!
# The F3b bridge in terms of the old project's evaluation functions

`evalIntegerList` (old D12 entries, `List ℤ` via `listPolynomial`) and `evalRationalList` (old denominators)
agree with `evalZ`, so `rowBridge_sound` / `denOk_sound` speak about the old literals.

Note: in `evalRationalList_div` the binder of `fun z => (z : ℚ) / dq` is elaborated as `z : ℚ`, so the list is
`dz` coerced to `List ℚ` (List monad) and then divided; `evalRationalList_div'` is the same fact with an explicit
`z : ℤ` binder (`(dz.map fun z : ℤ => (z : ℚ) / dq)`).
-/

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed

theorem evalIntegerList_eq_evalZ (h : List ℤ) (a : ℝ) : Blueprint.CAP.evalIntegerList h a = evalZ h a := by
  unfold Blueprint.CAP.evalIntegerList
  induction h with
  | nil => rw [Blueprint.CAP.listPolynomial_nil, Polynomial.eval₂_zero, Bridge.evalZ_nil]
  | cons c l ih =>
    rw [Blueprint.CAP.listPolynomial_cons, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X, ih, Bridge.evalZ_cons, eq_intCast]

theorem evalRationalList_div' (dz : List ℤ) (dq : ℕ) (a : ℝ) :
    Blueprint.CAP.evalRationalList (dz.map fun z : ℤ => (z : ℚ) / dq) a = evalZ dz a / dq := by
  induction dz with
  | nil => simp only [List.map_nil, Bridge.evalZ_nil, zero_div, Blueprint.CAP.evalRationalList]
  | cons c l ih =>
    simp only [List.map_cons, Blueprint.CAP.evalRationalList]
    rw [ih, Bridge.evalZ_cons]
    push_cast
    ring

/-- the coercion `List ℤ → List ℚ` (through the List monad) is `map Int.cast` -/
theorem Bridge.coe_list_int_rat (dz : List ℤ) : (dz : List ℚ) = dz.map (fun z : ℤ => (z : ℚ)) := by
  induction dz with
  | nil => rfl
  | cons c l ih =>
    rw [List.map_cons, ← ih]
    rfl

theorem evalRationalList_div (dz : List ℤ) (dq : ℕ) (hdq : 0 < dq) (a : ℝ) :
    Blueprint.CAP.evalRationalList (dz.map fun z => (z : ℚ) / dq) a = evalZ dz a / dq := by
  have _hdq := hdq
  rw [Bridge.coe_list_int_rat, List.map_map]
  exact evalRationalList_div' dz dq a

end ThomsonCompact.Floor.B
