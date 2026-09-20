import Coulomb8.Columns.C191
import Coulomb8.CoefficientMatrix.C23

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C191

theorem coefficient_list : Columns.C191.coefficients=List.ofFn CoefficientMatrix.column191 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C191
