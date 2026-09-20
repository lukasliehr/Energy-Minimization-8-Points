import Coulomb8.Columns.C121
import Coulomb8.CoefficientMatrix.C15

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C121

theorem coefficient_list : Columns.C121.coefficients=List.ofFn CoefficientMatrix.column121 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C121
