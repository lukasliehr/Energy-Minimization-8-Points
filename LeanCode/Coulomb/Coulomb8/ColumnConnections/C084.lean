import Coulomb8.Columns.C084
import Coulomb8.CoefficientMatrix.C10

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C084

theorem coefficient_list : Columns.C084.coefficients=List.ofFn CoefficientMatrix.column84 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C084
