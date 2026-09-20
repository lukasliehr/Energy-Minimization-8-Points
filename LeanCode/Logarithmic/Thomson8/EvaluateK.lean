import Thomson8.Certificate

namespace Thomson8.Poly

def evalK (p : Poly) (u v t : K) : K := K.sum (p.map fun (e,c) =>
  K.mul c (K.mul (K.mul (K.pow u e.u) (K.pow v e.v)) (K.pow t e.t)))

theorem eval_evalK (p : Poly) (u v t : K) :
    (p.evalK u v t).eval = p.eval u.eval v.eval t.eval := by
  simp [evalK,eval,Exponent.eval,Function.comp_def]

end Thomson8.Poly
