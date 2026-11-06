import ThomsonNegative.Certificate.MatrixCellSound
import ThomsonNegative.Certificate.Cells.q01.MatrixData
import ThomsonNegative.Certificate.Cells.q01.Basis
import ThomsonNegative.Certificate.Cells.q01.Residual
import ThomsonNegative.Certificate.Cells.q01.Gram0
import ThomsonNegative.Certificate.Cells.q01.Check0
import ThomsonNegative.Certificate.Cells.q01.Gram1
import ThomsonNegative.Certificate.Cells.q01.Check1
import ThomsonNegative.Certificate.Cells.q01.Gram2
import ThomsonNegative.Certificate.Cells.q01.Check2
import ThomsonNegative.Certificate.Cells.q01.Gram3
import ThomsonNegative.Certificate.Cells.q01.Check3
import ThomsonNegative.Certificate.Cells.q01.Gram4
import ThomsonNegative.Certificate.Cells.q01.Check4
import ThomsonNegative.Certificate.Cells.q01.Gram5
import ThomsonNegative.Certificate.Cells.q01.Check5
import ThomsonNegative.Certificate.Cells.q01.Gram6
import ThomsonNegative.Certificate.Cells.q01.Check6
import ThomsonNegative.Certificate.Cells.q01.Gram7
import ThomsonNegative.Certificate.Cells.q01.Check7

noncomputable section
namespace ThomsonNegative.Certificate.Cells.q01
open ThomsonNegative.Compact.Packed
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
theorem matrix_checked : matrixData.Checked (0:Fin 5) := by
  constructor
  · exact basis_gate_pass
  · intro b; fin_cases b
    · exact gram_gate_0
    · exact gram_gate_1
    · exact gram_gate_2
    · exact gram_gate_3
    · exact gram_gate_4
    · exact gram_gate_5
    · exact gram_gate_6
    · exact gram_gate_7
  · intro b; fin_cases b
    · exact image0_gate_pass
    · exact image1_gate_pass
    · exact image2_gate_pass
    · exact image3_gate_pass
    · exact image4_gate_pass
    · exact image5_gate_pass
    · exact image6_gate_pass
    · exact image7_gate_pass
  · intro b; fin_cases b
    · exact checkpoint0_pass
    · exact checkpoint1_pass
    · exact checkpoint2_pass
    · exact checkpoint3_pass
    · exact checkpoint4_pass
    · exact checkpoint5_pass
    · exact checkpoint6_pass
    · exact checkpoint7_pass
  · exact residual_checkpoint_pass
def initialFamily (t : ℝ) : Structure.GramFamily := matrixData.initialFamily t
def sourceResidual (t : ℝ) : Structure.ChartSpace := matrixData.sourceResidual (0:Fin 5) t
theorem residual_encl (r : Fin 68) :
    Encl context (residualCheckpoint.getD r.val zeroTM) (fun t => sourceResidual t r) :=
  MatrixCell.residual_encl matrix_checked r
theorem metric_order (b : Fin 8) : (matrixData.metric b.val).order=Structure.blockSize b := by
  fin_cases b <;> rfl
#print axioms matrix_checked
#print axioms residual_encl
end ThomsonNegative.Certificate.Cells.q01
