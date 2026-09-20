import Thomson8.Certificate

namespace Thomson8

def gramDet3 (u v t : ℝ) : ℝ := 1+2*u*v*t-u^2-v^2-t^2

def gramResidual (u v t a b c : ℝ) : ℝ :=
  (1-t^2)*a^2+(1-v^2)*b^2+(1-u^2)*c^2+
    2*(v*t-u)*a*b+2*(u*t-v)*a*c+2*(u*v-t)*b*c-gramDet3 u v t

def gramDet3K (u v t : K) : K := K.sum [K.one,K.scale 2 (K.mul (K.mul u v) t),
  K.neg (K.pow u 2),K.neg (K.pow v 2),K.neg (K.pow t 2)]

def gramResidualK (u v t a b c : K) : K := K.sum [
  K.mul (K.add K.one (K.neg (K.pow t 2))) (K.pow a 2),
  K.mul (K.add K.one (K.neg (K.pow v 2))) (K.pow b 2),
  K.mul (K.add K.one (K.neg (K.pow u 2))) (K.pow c 2),
  K.scale 2 (K.mul (K.mul (K.add (K.mul v t) (K.neg u)) a) b),
  K.scale 2 (K.mul (K.mul (K.add (K.mul u t) (K.neg v)) a) c),
  K.scale 2 (K.mul (K.mul (K.add (K.mul u v) (K.neg t)) b) c),
  K.neg (gramDet3K u v t)]

theorem eval_gramDet3K (u v t : K) : (gramDet3K u v t).eval=gramDet3 u.eval v.eval t.eval := by
  simp [gramDet3K,gramDet3]
  ring

theorem eval_gramResidualK (u v t a b c : K) :
    (gramResidualK u v t a b c).eval=gramResidual u.eval v.eval t.eval a.eval b.eval c.eval := by
  simp [gramResidualK,gramResidual,eval_gramDet3K]
  ring

end Thomson8
