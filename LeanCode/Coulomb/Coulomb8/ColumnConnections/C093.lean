import Coulomb8.Columns.C093
import Coulomb8.CoefficientMatrix.C11

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C093

theorem coefficient_list : Columns.C093.coefficients=List.ofFn CoefficientMatrix.column93 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C093
