import Coulomb8.Columns.C124
import Coulomb8.CoefficientMatrix.C15

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C124

theorem coefficient_list : Columns.C124.coefficients=List.ofFn CoefficientMatrix.column124 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C124
