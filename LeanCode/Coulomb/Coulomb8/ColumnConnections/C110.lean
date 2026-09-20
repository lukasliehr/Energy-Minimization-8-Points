import Coulomb8.Columns.C110
import Coulomb8.CoefficientMatrix.C13

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C110

theorem coefficient_list : Columns.C110.coefficients=List.ofFn CoefficientMatrix.column110 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C110
