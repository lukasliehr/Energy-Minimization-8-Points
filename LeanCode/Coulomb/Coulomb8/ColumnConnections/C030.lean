import Coulomb8.Columns.C030
import Coulomb8.CoefficientMatrix.C03

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C030

theorem coefficient_list : Columns.C030.coefficients=List.ofFn CoefficientMatrix.column30 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C030
