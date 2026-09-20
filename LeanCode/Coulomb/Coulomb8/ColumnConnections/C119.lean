import Coulomb8.Columns.C119
import Coulomb8.CoefficientMatrix.C14

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C119

theorem coefficient_list : Columns.C119.coefficients=List.ofFn CoefficientMatrix.column119 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C119
