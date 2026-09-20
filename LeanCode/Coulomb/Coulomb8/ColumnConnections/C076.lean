import Coulomb8.Columns.C076
import Coulomb8.CoefficientMatrix.C09

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C076

theorem coefficient_list : Columns.C076.coefficients=List.ofFn CoefficientMatrix.column76 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C076
