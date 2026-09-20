import Coulomb8.Columns.C138
import Coulomb8.CoefficientMatrix.C17

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C138

theorem coefficient_list : Columns.C138.coefficients=List.ofFn CoefficientMatrix.column138 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C138
