import Thomson8.BlockValue
import Thomson8.SymmetryLinearity
import Thomson8.MatrixPairing

namespace Thomson8.Block

theorem sos_column_eval (b : Block) (hm : b.moment=false) (i j : ℕ) (u v t : ℝ) :
    (b.column i j).eval u v t = Poly.symEval (fun u v t =>
      (if b.weighted then 1-u^2 else 1)*
        ((b.polys.getD i []).eval u v t*(b.polys.getD j []).eval u v t)) u v t := by
  cases hw : b.weighted <;> simp [column,hm,hw,Poly.eval_symmetrize,Poly.symEval,Exponent.eval]
  ring

noncomputable def polyVector (b : Block) (u v t : ℝ) : Fin b.n → ℝ :=
  fun i => (b.polys.getD i []).eval u v t

theorem sos_value (b : Block) (hm : b.moment=false) (u v t : ℝ) :
    b.value u v t = Poly.symEval (fun u v t => (if b.weighted then 1-u^2 else 1)*
      quadratic b.matrix (b.polyVector u v t)) u v t := by
  rw [value_eq_columns]
  simp_rw [sos_column_eval b hm]
  have hf (i : Fin b.n) :
      (∑ j : Fin b.n, b.matrix i j * Poly.symEval (fun u v t =>
        (if b.weighted then 1-u^2 else 1)*
          ((b.polys.getD i []).eval u v t*(b.polys.getD j []).eval u v t)) u v t) =
      Poly.symEval (fun u v t => ∑ j : Fin b.n, b.matrix i j *
        ((if b.weighted then 1-u^2 else 1)*
          ((b.polys.getD i []).eval u v t*(b.polys.getD j []).eval u v t))) u v t := by
    rw [Poly.symEval_fin_sum]
    simp_rw [Poly.symEval_const_mul]
  simp_rw [hf]
  rw [←Poly.symEval_fin_sum]
  congr 1
  funext u v t
  simp only [quadratic,polyVector,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sos_value_nonneg (b : Block) (hm : b.moment=false) (hb : b.matrix.PosSemidef)
    (u v t : ℝ) (hu : -1 ≤ u ∧ u ≤ 1) (hv : -1 ≤ v ∧ v ≤ 1) (ht : -1 ≤ t ∧ t ≤ 1) :
    0 ≤ b.value u v t := by
  rw [sos_value b hm]
  have h (u v t : ℝ) (hu : -1 ≤ u ∧ u ≤ 1) :
      0 ≤ (if b.weighted then 1-u^2 else 1)*quadratic b.matrix (b.polyVector u v t) := by
    apply mul_nonneg _ (quadratic_nonneg b.matrix hb _)
    cases b.weighted <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · norm_num
    · nlinarith [mul_nonneg (by linarith : 0≤1-u) (by linarith : 0≤1+u)]
  exact Poly.symEval_nonneg u v t (h u v t hu) (h u t v hu) (h v u t hv)
    (h t u v ht) (h v t u hv) (h t v u ht)

#print axioms sos_value_nonneg

end Thomson8.Block
