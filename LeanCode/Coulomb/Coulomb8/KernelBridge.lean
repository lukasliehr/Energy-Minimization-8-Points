import Coulomb8.Repeated
import Coulomb8.Symmetry
import Thomson8.RCounting
import Thomson8.SymmetryLinearity

namespace Coulomb8
open scoped BigOperators

namespace Poly

theorem symEval_fin_sum {α : Type*} [Fintype α] (f : α → ℝ → ℝ → ℝ → ℝ) (u v t : ℝ) :
    symEval (fun u v t => ∑ i, f i u v t) u v t=∑ i, symEval (f i) u v t :=
  Thomson8.Poly.symEval_fin_sum f u v t

theorem symEval_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ → ℝ) (u v t : ℝ) :
    symEval (fun u v t => c*f u v t) u v t=c*symEval f u v t :=
  Thomson8.Poly.symEval_const_mul c f u v t

theorem symEval_nonneg {f : ℝ → ℝ → ℝ → ℝ} (u v t : ℝ)
    (h0 : 0≤f u v t) (h1 : 0≤f u t v) (h2 : 0≤f v u t)
    (h3 : 0≤f t u v) (h4 : 0≤f v t u) (h5 : 0≤f t v u) :
    0≤symEval f u v t := Thomson8.Poly.symEval_nonneg u v t h0 h1 h2 h3 h4 h5

end Poly

theorem kernelQ_polynomial (k : ℕ) (u v t : ℝ) :
    (Block.Q k).eval u v t=Thomson8.kernelQ k u v t := by
  induction k using Nat.twoStepInduction with
  | zero => simp [Block.Q,Thomson8.kernelQ]
  | one => simp [Block.Q,Thomson8.kernelQ,Block.tangentBase,Exponent.eval,sub_eq_add_neg]
  | more k hk hk1 =>
    simp [Block.Q,Thomson8.kernelQ,Block.tangentBase,Block.tangentFactor,Exponent.eval,hk,hk1]
    ring

theorem S_eval_bridge (k i j : ℕ) (u v t : ℝ) :
    (Block.S k i j).eval u v t=(Thomson8.Block.S k i j).eval u v t := by
  rw [Thomson8.S_eval]
  simp only [Block.S,Poly.eval_symmetrize]
  have he : (Poly.shift ⟨i,j,0⟩ K.one (Block.Q k)).eval=
      fun u v t => u^i*v^j*Thomson8.kernelQ k u v t := by
    funext u v t
    simp [Poly.eval_shift,Exponent.eval,kernelQ_polynomial]
  rw [he]
  rfl

theorem R_eval_bridge (k i j : ℕ) (u v t : ℝ) :
    (Block.R k i j).eval u v t=(Thomson8.Block.R k i j).eval u v t := by
  rw [Thomson8.R_eval]
  simp only [Block.R,Poly.eval_sum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    Poly.eval_scale,K.eval_ofRat,Poly.eval_repeated_zero,Poly.eval_repeated_one,
    Poly.eval_repeated_two,Poly.eval_const,S_eval_bridge]
  by_cases hk : k=0 <;> simp [hk] <;> ring

theorem sum_R_eq_moment (m k : ℕ) (y : Configuration) (hy : ∀ i, ‖y i‖=1) (i j : Fin m) :
    Thomson8.distinctSum (Thomson8.onTriples y (Block.R k i j).eval)=
      6*Thomson8.momentMatrix m k y i j := by
  have he : (Block.R k i j).eval=(Thomson8.Block.R k i j).eval := by
    funext u v t; exact R_eval_bridge k i j u v t
  rw [he]
  exact Thomson8.sum_R_eq_moment m k y hy i j

end Coulomb8

#print axioms Coulomb8.sum_R_eq_moment
