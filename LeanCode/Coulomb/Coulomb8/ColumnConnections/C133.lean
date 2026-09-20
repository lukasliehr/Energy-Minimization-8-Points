import Coulomb8.Columns.C133
import Coulomb8.CoefficientMatrix.C16

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C133

theorem coefficient_list : Columns.C133.coefficients=List.ofFn CoefficientMatrix.column133 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C133
