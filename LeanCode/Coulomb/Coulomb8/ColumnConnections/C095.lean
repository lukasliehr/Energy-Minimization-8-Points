import Coulomb8.Columns.C095
import Coulomb8.CoefficientMatrix.C11

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C095

theorem coefficient_list : Columns.C095.coefficients=List.ofFn CoefficientMatrix.column95 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C095
