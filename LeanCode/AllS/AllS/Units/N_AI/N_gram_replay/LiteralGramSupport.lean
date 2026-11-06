import AllS.Units.N_AI.N_data.LiteralSchema
import AllS.Units.N_AI.N_gram_replay.N_uncorrected_floor

noncomputable section
namespace Blueprint.CAP

/-- Source metric rows contain a strict lower triangle, followed independently
by the exact powers of two on the diagonal. Row indexing is zero based. -/
def literalMetric (b : Literals.Block) (bits : ℕ) :
    Matrix (Fin b.order) (Fin b.order) ℝ := fun i j =>
  if j < i then (b.strictLower.getD (i.val*(i.val-1)/2+j.val) 0 : ℝ)/(2:ℝ)^bits
  else if i=j then (2:ℝ)^(b.diagonalExponents.getD i.val 0) else 0

/-- Each Bernstein square factor is a lower-triangular integer matrix in
row-major packed order. Missing data decode to zero and cannot strengthen the
positive floor; shape and literal correspondence are checked separately. -/
def literalFactor (b : Literals.Block) (bits j : ℕ) :
    Matrix (Fin b.order) (Fin b.order) ℝ := fun r c =>
  if c ≤ r then ((b.factors.getD j []).getD (r.val*(r.val+1)/2+c.val) 0 : ℝ)/(2:ℝ)^bits
  else 0

def literalGram (cell : Literals.Cell) (b : Literals.Block) (x : ℝ) :
    Matrix (Fin b.order) (Fin b.order) ℝ :=
  gramFromFactors ((2:ℝ)^cell.floorExponent) (literalMetric b cell.metricBits)
    (fun j : Fin (cell.bernsteinDegree+1) => literalFactor b cell.factorBits j.val) x

theorem literalMetric_lower (b : Literals.Block) (bits : ℕ) :
    (literalMetric b bits).IsLowerTriangular := by
  intro i j hij
  change i < j at hij
  simp only [literalMetric,if_neg (not_lt_of_ge hij.le),if_neg (ne_of_lt hij)]

theorem literalMetric_diagonal_pos (b : Literals.Block) (bits : ℕ)
    (i : Fin b.order) : 0 < literalMetric b bits i i := by
  simp only [literalMetric,lt_self_iff_false,if_false,ite_true]
  exact zpow_pos (by norm_num) _

theorem literalGram_floor (cell : Literals.Cell) (b : Literals.Block)
    (x : ℝ) (hx : x ∈ cellDomain) :
    (literalGram cell b x-((2:ℝ)^cell.floorExponent) •
      (literalMetric b cell.metricBits*(literalMetric b cell.metricBits).transpose)).PosSemidef ∧
    (literalGram cell b x).PosDef := by
  exact gram_replay_uncorrected_floor _ _ _ (zpow_pos (by norm_num) _)
    (literalMetric_lower b _) (literalMetric_diagonal_pos b _) x hx

#print axioms literalMetric_lower
#print axioms literalMetric_diagonal_pos
#print axioms literalGram_floor
end Blueprint.CAP
