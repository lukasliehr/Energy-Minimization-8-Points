import Thomson8.KernelPositivity
import Thomson8.TripleSymmetry

namespace Thomson8

open scoped InnerProductSpace

noncomputable def powerFeatures (m : ℕ) (x : Point) (y : Configuration) :
    Matrix (Fin m) Index ℝ := fun a j => ⟪x,y j⟫_ℝ^a.val

noncomputable def momentMatrix (m k : ℕ) (y : Configuration) : Matrix (Fin m) (Fin m) ℝ :=
  ∑ i : Index, powerFeatures m (y i) y * sphericalKernel (y i) y k *
    (powerFeatures m (y i) y).transpose

theorem momentMatrix_posSemidef (m k : ℕ) (y : Configuration) (hy : ∀ i, ‖y i‖=1) :
    (momentMatrix m k y).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro i _
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (sphericalKernel_posSemidef (y i) (hy i) y hy k).mul_mul_conjTranspose_same
      (powerFeatures m (y i) y)

theorem momentMatrix_entry (m k : ℕ) (y : Configuration) (a b : Fin m) :
    momentMatrix m k y a b = tripleSum (onTriples y (fun u v t => u^a.val*v^b.val*kernelQ k u v t)) := by
  simp only [momentMatrix,Matrix.sum_apply,Matrix.mul_apply,Matrix.transpose_apply,
    powerFeatures,sphericalKernel,tripleSum,onTriples,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem S_eval (k a b : ℕ) (u v t : ℝ) :
    (Block.S k a b).eval u v t = Poly.symEval (fun u v t => u^a*v^b*kernelQ k u v t) u v t := by
  simp [Block.S,Poly.eval_symmetrize,Poly.symEval,Poly.eval_shift,Exponent.eval,kernelQ_polynomial]

theorem momentMatrix_eq_sum_S (m k : ℕ) (y : Configuration) (a b : Fin m) :
    momentMatrix m k y a b = tripleSum (onTriples y (Block.S k a b).eval) := by
  rw [momentMatrix_entry]
  have h : (Block.S k a b).eval = Poly.symEval (fun u v t => u^a.val*v^b.val*kernelQ k u v t) :=
    funext fun u => funext fun v => funext fun t => S_eval _ _ _ _ _ _
  rw [h,tripleSum_sym]

#print axioms momentMatrix_posSemidef
#print axioms momentMatrix_eq_sum_S

end Thomson8
