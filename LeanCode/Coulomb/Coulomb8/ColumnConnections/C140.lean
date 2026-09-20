import Coulomb8.Columns.C140
import Coulomb8.CoefficientMatrix.C17

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C140

theorem coefficient_list : Columns.C140.coefficients=List.ofFn CoefficientMatrix.column140 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C140
