import Coulomb8.Columns.C175
import Coulomb8.CoefficientMatrix.C21

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C175

theorem coefficient_list : Columns.C175.coefficients=List.ofFn CoefficientMatrix.column175 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C175
