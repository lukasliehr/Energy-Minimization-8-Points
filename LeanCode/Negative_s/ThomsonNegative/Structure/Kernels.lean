import ThomsonNegative.Structure.Basic
import ThomsonNegative.Geometry.GramSound

/-! Polynomial realizations of arbitrary moment mixtures and sums of squares. -/

noncomputable section
open scoped BigOperators

namespace ThomsonNegative.Structure

open MvPolynomial
open ThomsonNegative.Geometry.GenericMoments

def coordinatePerm : Fin 6 → Fin 3 → Fin 3 :=
  ![![0,1,2], ![0,2,1], ![1,0,2], ![2,0,1], ![1,2,0], ![2,1,0]]

def reynoldsPolynomial (p : Poly3) : Poly3 :=
  (1 / 6 : ℝ) • ∑ r : Fin 6, MvPolynomial.rename (coordinatePerm r) p

def kernelQPolynomial : ℕ → Poly3
  | 0 => 1
  | 1 => MvPolynomial.X 2 - MvPolynomial.X 0 * MvPolynomial.X 1
  | k + 2 => C 2 * (MvPolynomial.X 2 - MvPolynomial.X 0 * MvPolynomial.X 1) * kernelQPolynomial (k+1) -
      (1-MvPolynomial.X 0^2) * (1-MvPolynomial.X 1^2) * kernelQPolynomial k

def kernelSPolynomial (k i j : ℕ) : Poly3 :=
  reynoldsPolynomial (MvPolynomial.X 0^i * MvPolynomial.X 1^j * kernelQPolynomial k)

def repeatPolynomial (r : Fin 3) : Poly3 →ₐ[ℝ] Poly3 :=
  MvPolynomial.aeval ![MvPolynomial.X r, MvPolynomial.X r, 1]

def kernelRPolynomial (k i j : ℕ) : Poly3 :=
  C 6 * kernelSPolynomial k i j + repeatPolynomial 0 (kernelSPolynomial k i j) +
    repeatPolynomial 1 (kernelSPolynomial k i j) +
    repeatPolynomial 2 (kernelSPolynomial k i j) + C ((if k=0 then 1 else 0)/7 : ℝ)

theorem kernelQPolynomial_eval (k : ℕ) (u : Fin 3 → ℝ) :
    MvPolynomial.eval u (kernelQPolynomial k) = kernelQ k (u 0) (u 1) (u 2) := by
  induction k using Nat.twoStepInduction with
  | zero => simp [kernelQPolynomial, kernelQ]
  | one => simp [kernelQPolynomial, kernelQ]
  | more k hk hk1 => simp [kernelQPolynomial, kernelQ, hk, hk1]

theorem reynoldsPolynomial_eval (p : Poly3) (u : Fin 3 → ℝ) :
    MvPolynomial.eval u (reynoldsPolynomial p) =
      symEval (fun x y z => MvPolynomial.eval ![x,y,z] p) (u 0) (u 1) (u 2) := by
  have hcomp (i j k : Fin 3) : (fun x => u (![i,j,k] x)) = ![u i,u j,u k] := by
    funext x
    fin_cases x <;> rfl
  simp [reynoldsPolynomial, MvPolynomial.eval_rename, Fin.sum_univ_succ,
    coordinatePerm, symEval, Function.comp_def, hcomp]
  ring

theorem kernelSPolynomial_eval (k i j : ℕ) (u : Fin 3 → ℝ) :
    MvPolynomial.eval u (kernelSPolynomial k i j) = Sfun k i j (u 0) (u 1) (u 2) := by
  rw [kernelSPolynomial, reynoldsPolynomial_eval]
  simp [Sfun, symEval, kernelQPolynomial_eval]

theorem eval_aeval_polynomial (x : Fin 3 → ℝ) (g : Fin 3 → Poly3) (p : Poly3) :
    MvPolynomial.eval x (MvPolynomial.aeval g p) =
      MvPolynomial.eval (fun i => MvPolynomial.eval x (g i)) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X, hp]

theorem repeatPolynomial_eval (r : Fin 3) (p : Poly3) (u : Fin 3 → ℝ) :
    MvPolynomial.eval u (repeatPolynomial r p) = MvPolynomial.eval ![u r,u r,1] p := by
  rw [repeatPolynomial, eval_aeval_polynomial]
  apply congrArg (fun v : Fin 3 → ℝ => MvPolynomial.eval v p)
  funext i
  fin_cases i <;> simp

theorem kernelRPolynomial_eval (k i j : ℕ) (u : Fin 3 → ℝ) :
    MvPolynomial.eval u (kernelRPolynomial k i j) = Rfun k i j (u 0) (u 1) (u 2) := by
  simp [kernelRPolynomial, Rfun, repeatPolynomial_eval, kernelSPolynomial_eval]

def momentPolynomial {n m : ℕ} (k : ℕ) (B : Matrix (Fin n) (Fin m) ℝ) :
    Matrix (Fin m) (Fin m) Poly3 := fun i j =>
  ∑ r, ∑ s, C (B r i * B s j) * kernelRPolynomial k r.val s.val

theorem momentPolynomial_eval {n m : ℕ} (k : ℕ) (B : Matrix (Fin n) (Fin m) ℝ)
    (i j : Fin m) (u : Fin 3 → ℝ) :
    MvPolynomial.eval u (momentPolynomial k B i j) =
      ∑ r, ∑ s, B r i * Rfun k r.val s.val (u 0) (u 1) (u 2) * B s j := by
  simp only [momentPolynomial, map_sum, map_mul, MvPolynomial.eval_C, kernelRPolynomial_eval]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  ring

theorem momentPolynomial_realization {n m : ℕ} (k : ℕ) (B : Matrix (Fin n) (Fin m) ℝ) :
    ThomsonNegative.Geometry.BlockRealization (momentPolynomial k B) :=
  .moment n k B (momentPolynomial_eval k B)

def squarePolynomial {ι : Type*} [Fintype ι] {m : ℕ}
    (w : ι → ℝ) (f : ι → Fin m → Poly3) : Matrix (Fin m) (Fin m) Poly3 :=
  fun i j => ∑ r, C (w r) * f r i * f r j

theorem squarePolynomial_realization {ι : Type*} [Fintype ι] {m : ℕ}
    (w : ι → ℝ) (f : ι → Fin m → Poly3) (hw : ∀ r, 0 ≤ w r) :
    ThomsonNegative.Geometry.BlockRealization (squarePolynomial w f) := by
  classical
  let e := (Fintype.equivFin ι).symm
  refine .sos (Fintype.card ι) (w ∘ e)
    (fun r u i => MvPolynomial.eval u (f (e r) i)) (fun r => hw (e r)) ?_
  intro i j u
  simp only [squarePolynomial, map_sum, map_mul, MvPolynomial.eval_C, Function.comp_apply]
  exact (Equiv.sum_comp e (fun r => w r * MvPolynomial.eval u (f r i) *
    MvPolynomial.eval u (f r j))).symm

end ThomsonNegative.Structure
