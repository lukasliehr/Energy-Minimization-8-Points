import Coulomb8.Columns.C143
import Coulomb8.CoefficientMatrix.C17

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C143

theorem coefficient_list : Columns.C143.coefficients=List.ofFn CoefficientMatrix.column143 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C143
