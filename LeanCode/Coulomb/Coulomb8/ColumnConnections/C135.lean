import Coulomb8.Columns.C135
import Coulomb8.CoefficientMatrix.C16

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C135

theorem coefficient_list : Columns.C135.coefficients=List.ofFn CoefficientMatrix.column135 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C135
