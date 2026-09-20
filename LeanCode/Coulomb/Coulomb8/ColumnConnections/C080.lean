import Coulomb8.Columns.C080
import Coulomb8.CoefficientMatrix.C10

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C080

theorem coefficient_list : Columns.C080.coefficients=List.ofFn CoefficientMatrix.column80 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C080
