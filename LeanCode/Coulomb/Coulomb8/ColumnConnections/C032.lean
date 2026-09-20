import Coulomb8.Columns.C032
import Coulomb8.CoefficientMatrix.C04

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C032

theorem coefficient_list : Columns.C032.coefficients=List.ofFn CoefficientMatrix.column32 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C032
