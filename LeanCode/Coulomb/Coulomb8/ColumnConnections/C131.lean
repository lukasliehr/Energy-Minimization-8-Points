import Coulomb8.Columns.C131
import Coulomb8.CoefficientMatrix.C16

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C131

theorem coefficient_list : Columns.C131.coefficients=List.ofFn CoefficientMatrix.column131 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C131
