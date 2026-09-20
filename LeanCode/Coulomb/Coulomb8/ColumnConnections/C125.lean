import Coulomb8.Columns.C125
import Coulomb8.CoefficientMatrix.C15

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C125

theorem coefficient_list : Columns.C125.coefficients=List.ofFn CoefficientMatrix.column125 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C125
