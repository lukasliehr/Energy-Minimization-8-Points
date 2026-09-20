import Coulomb8.Columns.C184
import Coulomb8.CoefficientMatrix.C23

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C184

theorem coefficient_list : Columns.C184.coefficients=List.ofFn CoefficientMatrix.column184 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C184
