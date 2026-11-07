import ThomsonNegative.Certificate.ResidualKernel
import ThomsonNegative.Certificate.StoredKernel

/-! A cell contains factors and a few checked model boundaries, never a trace. -/
namespace ThomsonNegative.Certificate
open ThomsonNegative.Compact.Packed

structure MatrixCell where
  metric : Nat → FactorData
  factor : Nat → Nat → FactorData
  checkpoint : Nat → List TM
  residualCheckpoint : List TM

def MatrixCell.context : Ctx := mkCtx 10 384 448 1024
def MatrixCell.tau : TM := ofPQ MatrixCell.context
  (Nat.shiftLeft MatrixCell.context.twoS MatrixCell.context.W) 0 0

def MatrixCell.initial (d : MatrixCell) (b : Nat) : TMMatrix :=
  blockTM MatrixCell.context (BasisLayout.freeOrder b) 10 11 MatrixCell.tau (d.metric b) (d.factor b)

def MatrixCell.images (d : MatrixCell) : List (List TM) := (List.range 8).map d.checkpoint

end ThomsonNegative.Certificate
