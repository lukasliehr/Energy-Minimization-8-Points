import Coulomb8.Columns.C141
import Coulomb8.CoefficientMatrix.C17

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C141

theorem coefficient_list : Columns.C141.coefficients=List.ofFn CoefficientMatrix.column141 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C141
