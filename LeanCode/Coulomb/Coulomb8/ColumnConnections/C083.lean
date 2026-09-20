import Coulomb8.Columns.C083
import Coulomb8.CoefficientMatrix.C10

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C083

theorem coefficient_list : Columns.C083.coefficients=List.ofFn CoefficientMatrix.column83 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C083
