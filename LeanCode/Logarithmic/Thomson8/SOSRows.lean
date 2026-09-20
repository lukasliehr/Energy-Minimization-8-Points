import Thomson8.Rows
import Thomson8.Symmetry

namespace Thomson8.Block

noncomputable def sosRowValue (b : Block) (i ell : ℕ) (u v t : ℝ) : ℝ :=
  ((List.range b.n).map fun j => (b.entry i j ell).eval *
    Poly.symEval (fun u v t =>
      (if b.weighted then 1-u^2 else 1) *
      ((b.polys.getD i []).eval u v t * (b.polys.getD j []).eval u v t)) u v t).sum

theorem eval_sos_row (b : Block) (hm : b.moment=false) (i ell : ℕ) (u v t : ℝ) :
    (b.rowComponent i ell).eval u v t = b.sosRowValue i ell u v t := by
  cases hw : b.weighted <;>
    simp [rowComponent, column, hm, hw, sosRowValue, Poly.eval_sum,
      Poly.eval_symmetrize, Poly.symEval, Exponent.eval, sub_eq_add_neg, Function.comp_def]

end Thomson8.Block
