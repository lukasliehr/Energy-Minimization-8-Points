import Coulomb8.Columns.C137
import Coulomb8.CoefficientMatrix.C17

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C137

theorem coefficient_list : Columns.C137.coefficients=List.ofFn CoefficientMatrix.column137 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C137
