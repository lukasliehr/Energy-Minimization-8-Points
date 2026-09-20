import Thomson8.Certificate
import Mathlib.Analysis.Complex.Basic

namespace Thomson8

noncomputable def kernelQ : ℕ → ℝ → ℝ → ℝ → ℝ
  | 0, _,_,_ => 1
  | 1, u,v,t => t-u*v
  | k+2, u,v,t => 2*(t-u*v)*kernelQ (k+1) u v t -
      (1-u^2)*(1-v^2)*kernelQ k u v t

theorem kernelQ_polynomial (k : ℕ) (u v t : ℝ) :
    (Block.Q k).eval u v t = kernelQ k u v t := by
  induction k using Nat.twoStepInduction with
  | zero => simp [Block.Q,kernelQ]
  | one => simp [Block.Q,kernelQ,Block.tangentBase,Exponent.eval,sub_eq_add_neg]
  | more k hk hk1 =>
    simp [Block.Q,kernelQ,Block.tangentBase,Block.tangentFactor,Exponent.eval,hk,hk1]
    ring

theorem real_power_recurrence (w : ℂ) (k : ℕ) :
    (w^(k+2)).re = 2*w.re*(w^(k+1)).re - Complex.normSq w*(w^k).re := by
  simp only [pow_succ, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

theorem kernelQ_complex (k : ℕ) (u v t : ℝ) (w : ℂ)
    (hr : w.re=t-u*v) (hn : Complex.normSq w=(1-u^2)*(1-v^2)) :
    kernelQ k u v t = (w^k).re := by
  induction k using Nat.twoStepInduction with
  | zero => simp [kernelQ]
  | one => simpa [kernelQ] using hr.symm
  | more k hk hk1 =>
    rw [kernelQ, hk, hk1, real_power_recurrence, hr, hn]

theorem complex_power_gram (z w : ℂ) (k : ℕ) :
    ((z*star w)^k).re = (z^k).re*(w^k).re + (z^k).im*(w^k).im := by
  change ((z * (starRingEnd ℂ) w)^k).re = _
  rw [mul_pow, ← map_pow]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

#print axioms kernelQ_complex

end Thomson8
