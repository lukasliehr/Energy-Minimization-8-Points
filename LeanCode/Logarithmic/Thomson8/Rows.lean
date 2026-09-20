import Thomson8.Data

namespace Thomson8.Block

private theorem sum_flatMap {α : Type*} (xs : List α) (f : α → List ℝ) :
    (xs.flatMap f).sum = (xs.map fun x => (f x).sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, List.sum_append, ih]

def rowComponent (b : Block) (i ell : ℕ) : Poly :=
  Poly.sum ((List.range b.n).map fun j => Poly.scale (b.entry i j ell) (b.column i j))

theorem component_eval_rows (b : Block) (ell : ℕ) (u v t : ℝ) :
    (b.component ell).eval u v t =
      ((List.range b.n).map fun i => (b.rowComponent i ell).eval u v t).sum := by
  simp [component, rowComponent, Poly.eval_sum, List.map_flatMap, sum_flatMap,
    Function.comp_def]

end Thomson8.Block
