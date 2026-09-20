import Coulomb8.Columns.C188
import Coulomb8.CoefficientMatrix.C23

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C188

theorem coefficient_list : Columns.C188.coefficients=List.ofFn CoefficientMatrix.column188 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C188
