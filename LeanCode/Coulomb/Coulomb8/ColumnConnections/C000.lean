import Coulomb8.Columns.C000
import Coulomb8.CoefficientMatrix.C00

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C000

theorem coefficient_list : Columns.C000.coefficients=List.ofFn CoefficientMatrix.column0 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C000
