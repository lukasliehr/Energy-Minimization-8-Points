import Coulomb8.Columns.C129
import Coulomb8.CoefficientMatrix.C16

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C129

theorem coefficient_list : Columns.C129.coefficients=List.ofFn CoefficientMatrix.column129 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C129
