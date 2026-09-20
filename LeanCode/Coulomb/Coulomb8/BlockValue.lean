import Coulomb8.BlockMatrix
import Coulomb8.KernelBridge
import Thomson8.FiniteSums

namespace Coulomb8.Block
open scoped BigOperators
open Thomson8 (list_sum_flatMap sum_range_eq_fin sum_four_exchange)

noncomputable def value (b : Block) (w : Fin 192 → ℝ) (u v t : ℝ) : ℝ :=
  ∑ i : Fin b.n, ∑ j : Fin b.n, b.matrixFrom w i j*(b.column i j).eval u v t

theorem moment_column_eval (b : Block) (hm : b.moment=true) (i j : ℕ) (u v t : ℝ) :
    (b.column i j).eval u v t =
      ∑ a : Fin b.basis.length, ∑ c : Fin b.basis.length,
        (b.basisEntry a i).eval*(b.basisEntry c j).eval*(R b.k a c).eval u v t := by
  simp [column,hm,Poly.eval_sum,List.map_flatMap,list_sum_flatMap,List.map_map,
    Function.comp_def,sum_range_eq_fin]

noncomputable def N (b : Block) : Matrix (Fin b.basis.length) (Fin b.n) ℝ :=
  fun a i => (b.basisEntry a i).eval

noncomputable def momentF (b : Block) (w : Fin 192 → ℝ) : Matrix (Fin b.basis.length) (Fin b.basis.length) ℝ :=
  b.N*b.matrixFrom w*b.N.transpose

theorem F_posSemidef (b : Block) (w : Fin 192 → ℝ) (hb : (b.matrixFrom w).PosSemidef) :
    (b.momentF w).PosSemidef := by
  simpa only [momentF,Matrix.conjTranspose_eq_transpose_of_trivial] using hb.mul_mul_conjTranspose_same b.N

theorem moment_value (b : Block) (w : Fin 192 → ℝ) (hm : b.moment=true) (u v t : ℝ) :
    b.value w u v t = ∑ a : Fin b.basis.length, ∑ c : Fin b.basis.length,
      b.momentF w a c*(R b.k a c).eval u v t := by
  unfold value
  simp_rw [moment_column_eval b hm,Finset.mul_sum]
  rw [sum_four_exchange]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  simp only [momentF,Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul,N]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end Coulomb8.Block
