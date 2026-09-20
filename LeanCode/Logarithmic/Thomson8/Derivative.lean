import Thomson8.Certificate
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

namespace Thomson8.Poly

def derivU (p : Poly) : Poly := p.map fun (e,c) =>
  (⟨e.u-1,e.v,e.t⟩,K.scale (e.u : ℚ) c)

theorem hasDerivAt_eval (p : Poly) (x v t : ℝ) :
    HasDerivAt (fun u => p.eval u v t) ((derivU p).eval x v t) x := by
  induction p with
  | nil => simpa [eval,derivU] using hasDerivAt_const x (0 : ℝ)
  | cons h p ih =>
    rcases h with ⟨e,c⟩
    have hpow := (hasDerivAt_pow e.u x).const_mul c.eval
    have hterm := (hpow.mul_const (v^e.v)).mul_const (t^e.t)
    convert! hterm.add ih using 1
    · ext u
      simp [eval,derivU,Exponent.eval]
      ring
    · simp [eval,derivU,Exponent.eval]
      ring

end Thomson8.Poly
