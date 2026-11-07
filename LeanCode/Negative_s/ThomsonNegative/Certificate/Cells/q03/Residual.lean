import ThomsonNegative.Certificate.ResidualKernel
import ThomsonNegative.Certificate.Cells.q03.ResidualData
import ThomsonNegative.Compact.Target.Cells.Q03
import ThomsonNegative.Certificate.Cells.q03.Stored0
import ThomsonNegative.Certificate.Cells.q03.Stored1
import ThomsonNegative.Certificate.Cells.q03.Stored2
import ThomsonNegative.Certificate.Cells.q03.Stored3
import ThomsonNegative.Certificate.Cells.q03.Stored4
import ThomsonNegative.Certificate.Cells.q03.Stored5
import ThomsonNegative.Certificate.Cells.q03.Stored6
import ThomsonNegative.Certificate.Cells.q03.Stored7

namespace ThomsonNegative.Certificate.Cells.q03
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
noncomputable def images : List (List Compact.Packed.TM) := [checkpoint0, checkpoint1, checkpoint2, checkpoint3, checkpoint4, checkpoint5, checkpoint6, checkpoint7]
noncomputable def residual : List Compact.Packed.TM := residualTM context images Compact.Target.Cells.Q03.data.coefficientCheckpoints
theorem residual_checkpoint_pass : sameModels residual residualCheckpoint = true := by decide +kernel
#print axioms residual_checkpoint_pass
end ThomsonNegative.Certificate.Cells.q03
