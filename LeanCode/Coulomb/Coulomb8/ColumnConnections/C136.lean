import Coulomb8.Columns.C136
import Coulomb8.CoefficientMatrix.C17

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C136

theorem coefficient_list : Columns.C136.coefficients=List.ofFn CoefficientMatrix.column136 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C136
