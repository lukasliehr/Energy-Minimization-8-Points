import Coulomb8.Columns.C120
import Coulomb8.CoefficientMatrix.C15

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C120

theorem coefficient_list : Columns.C120.coefficients=List.ofFn CoefficientMatrix.column120 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C120
