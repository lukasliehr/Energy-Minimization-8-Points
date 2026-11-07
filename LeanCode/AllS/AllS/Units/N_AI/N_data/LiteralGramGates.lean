import AllS.Units.N_AI.N_data.LiteralSchema
import AllS.Units.N_AI.N_data.RationalBernstein
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Order.Field.Rat

namespace Blueprint.CAP
open scoped BigOperators

def literalMetricQ (b : Literals.Block) (bits : ℕ) :
    Matrix (Fin b.order) (Fin b.order) ℚ := fun i j =>
  if j < i then (b.strictLower.getD (i.val*(i.val-1)/2+j.val) 0 : ℚ)/(2:ℚ)^bits
  else if i=j then (2:ℚ)^(b.diagonalExponents.getD i.val 0) else 0

def literalFactorQ (b : Literals.Block) (bits j : ℕ) :
    Matrix (Fin b.order) (Fin b.order) ℚ := fun r c =>
  if c ≤ r then ((b.factors.getD j []).getD (r.val*(r.val+1)/2+c.val) 0 : ℚ)/(2:ℚ)^bits
  else 0

/-- Exact coefficient formula for the original dyadic Bernstein square model.
This is a rational finite computation, with no floating-point intermediate. -/
def literalGramCoeffQ (cell : Literals.Cell) (b : Literals.Block) (k : ℕ) :
    Matrix (Fin b.order) (Fin b.order) ℚ := fun i j =>
  (if k=0 then (2:ℚ)^cell.floorExponent *
    (literalMetricQ b cell.metricBits*(literalMetricQ b cell.metricBits).transpose) i j else 0) +
  ∑ u : Fin (cell.bernsteinDegree+1),
    (literalFactorQ b cell.factorBits u.val*(literalFactorQ b cell.factorBits u.val).transpose) i j *
      (((cell.bernsteinDegree.choose u.val:ℚ)*(cell.bernsteinDegree.choose k:ℚ)/(2:ℚ)^cell.bernsteinDegree) *
        rationalBernsteinTransform cell.bernsteinDegree u.val k)

end Blueprint.CAP
