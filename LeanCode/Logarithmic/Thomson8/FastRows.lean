import Thomson8.SOSRows

namespace Thomson8.Poly

theorem symEval_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ → ℝ) (u v t : ℝ) :
    symEval (fun u v t => c*f u v t) u v t = c*symEval f u v t := by
  unfold symEval
  ring

theorem symEval_list_sum {α : Type*} (xs : List α) (f : α → ℝ → ℝ → ℝ → ℝ)
    (u v t : ℝ) :
    symEval (fun u v t => (xs.map fun j => f j u v t).sum) u v t =
      (xs.map fun j => symEval (f j) u v t).sum := by
  induction xs with
  | nil => simp [symEval]
  | cons a xs ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [show symEval (fun u v t => f a u v t + (xs.map fun j => f j u v t).sum) u v t =
      symEval (f a) u v t + symEval (fun u v t => (xs.map fun j => f j u v t).sum) u v t by
        unfold symEval; ring,ih]

end Thomson8.Poly

namespace Thomson8.Block

def fastRow (b : Block) (i ell : ℕ) : Poly :=
  let g := if b.weighted then
    Poly.add (Poly.const K.one) (Poly.scale (K.ofRat (-1)) (Poly.monomial ⟨2,0,0⟩))
    else Poly.const K.one
  Poly.symmetrize (Poly.mul (Poly.mul g (b.polys.getD i []))
    (Poly.sum ((List.range b.n).map fun j => Poly.scale (b.entry i j ell) (b.polys.getD j []))))

theorem fastRow_eval (b : Block) (hm : b.moment=false) (i ell : ℕ) (u v t : ℝ) :
    (b.rowComponent i ell).eval u v t = (b.fastRow i ell).eval u v t := by
  rw [eval_sos_row b hm]
  have hf (w : Bool) (u v t : ℝ) :
      (if w then 1-u^2 else 1) * (b.polys.getD i []).eval u v t *
        ((List.range b.n).map fun j => (b.entry i j ell).eval * (b.polys.getD j []).eval u v t).sum =
      ((List.range b.n).map fun j => (b.entry i j ell).eval *
        ((if w then 1-u^2 else 1) * ((b.polys.getD i []).eval u v t *
          (b.polys.getD j []).eval u v t))).sum := by
    generalize List.range b.n = xs
    induction xs with
    | nil => simp
    | cons j xs ih => simp only [List.map_cons,List.sum_cons]; rw [←ih]; ring
  have hfun := funext fun u => funext fun v => funext fun t => hf b.weighted u v t
  have he : (b.fastRow i ell).eval u v t =
      Poly.symEval (fun u v t => (if b.weighted then 1-u^2 else 1) *
        (b.polys.getD i []).eval u v t *
          ((List.range b.n).map fun j => (b.entry i j ell).eval * (b.polys.getD j []).eval u v t).sum) u v t := by
    cases hw : b.weighted <;>
      simp [fastRow,hw,Poly.eval_symmetrize,Poly.symEval,Exponent.eval,Function.comp_def]
    ring
  rw [he,hfun,Poly.symEval_list_sum]
  simp only [sosRowValue,Poly.symEval_const_mul]

end Thomson8.Block
