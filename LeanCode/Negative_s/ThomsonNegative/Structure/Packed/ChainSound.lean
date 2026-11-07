import ThomsonNegative.Structure.Packed.ChainKernel
import ThomsonNegative.Structure.Packed.MatrixSound

namespace ThomsonNegative.Structure.Exact
open ThomsonNegative.Structure.Packed

theorem ProductChain.step (c : ProductChain) (h : c.check=true) (k : Nat)
    (hk : k<c.length) (a : ℝ) :
    evalZ (recCoeffs (c.node (k+1))) a =
      evalZ (recCoeffs (c.node k)) a * evalZ (recCoeffs (c.factor k)) a := by
  have he := (c.equation k).sound (allBelow_spec _ _ h k hk) a
  simpa [ProductChain.equation, oneRecord_decode, evalZ, horner] using he.symm

theorem ProductChain.nonzero (c : ProductChain) (h : c.check=true) (a : ℝ)
    (hbase : evalZ (recCoeffs (c.node 0)) a ≠ 0)
    (hfactor : ∀ k, k<c.length → evalZ (recCoeffs (c.factor k)) a ≠ 0) :
    evalZ (recCoeffs (c.node c.length)) a ≠ 0 := by
  have all : ∀ n, n≤c.length → evalZ (recCoeffs (c.node n)) a ≠ 0 := by
    intro n
    induction n with
    | zero => intro _; exact hbase
    | succ n ih =>
      intro hn
      rw [c.step h n (by omega) a]
      exact mul_ne_zero (ih (by omega)) (hfactor n (by omega))
  exact all _ le_rfl

end ThomsonNegative.Structure.Exact
