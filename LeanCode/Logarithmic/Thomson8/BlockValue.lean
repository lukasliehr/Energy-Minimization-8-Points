import Thomson8.MatrixBounds
import Thomson8.Rows
import Thomson8.FiniteSums

namespace Thomson8.Block

noncomputable def value (b : Block) (u v t : ℝ) : ℝ :=
  ∑ ell : Fin 5, logValues ell * (b.component ell).eval u v t

theorem value_eq_columns (b : Block) (u v t : ℝ) :
    b.value u v t = ∑ i : Fin b.n, ∑ j : Fin b.n,
      b.matrix i j*(b.column i j).eval u v t := by
  simp only [value,component_eval_rows,rowComponent,Poly.eval_sum,List.map_map,
    Function.comp_def,Poly.eval_scale,sum_range_eq_fin,matrix,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro ell _
  ring

theorem moment_column_eval (b : Block) (hm : b.moment=true) (i j : ℕ) (u v t : ℝ) :
    (b.column i j).eval u v t =
      ∑ a : Fin b.basis.length, ∑ c : Fin b.basis.length,
        (b.basisEntry a i).eval*(b.basisEntry c j).eval*(R b.k a c).eval u v t := by
  simp [column,hm,Poly.eval_sum,List.map_flatMap,list_sum_flatMap,List.map_map,
    Function.comp_def,sum_range_eq_fin]

noncomputable def N (b : Block) : Matrix (Fin b.basis.length) (Fin b.n) ℝ :=
  fun a i => (b.basisEntry a i).eval

noncomputable def F (b : Block) : Matrix (Fin b.basis.length) (Fin b.basis.length) ℝ :=
  b.N*b.matrix*b.N.transpose

theorem F_posSemidef (b : Block) (hb : b.matrix.PosSemidef) : b.F.PosSemidef := by
  simpa only [F,Matrix.conjTranspose_eq_transpose_of_trivial] using hb.mul_mul_conjTranspose_same b.N

theorem moment_value (b : Block) (hm : b.moment=true) (u v t : ℝ) :
    b.value u v t = ∑ a : Fin b.basis.length, ∑ c : Fin b.basis.length,
      b.F a c*(R b.k a c).eval u v t := by
  rw [value_eq_columns]
  simp_rw [moment_column_eval b hm,Finset.mul_sum]
  rw [sum_four_exchange]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  simp only [F,Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul,N]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end Thomson8.Block
