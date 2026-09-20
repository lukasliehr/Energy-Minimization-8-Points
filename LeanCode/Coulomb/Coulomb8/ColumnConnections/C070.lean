import Coulomb8.Columns.C070
import Coulomb8.CoefficientMatrix.C08

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C070

theorem coefficient_list : Columns.C070.coefficients=List.ofFn CoefficientMatrix.column70 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C070
