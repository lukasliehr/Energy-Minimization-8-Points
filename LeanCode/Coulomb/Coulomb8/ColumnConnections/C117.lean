import Coulomb8.Columns.C117
import Coulomb8.CoefficientMatrix.C14

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C117

theorem coefficient_list : Columns.C117.coefficients=List.ofFn CoefficientMatrix.column117 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C117
