import Coulomb8.Columns.C128
import Coulomb8.CoefficientMatrix.C16

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C128

theorem coefficient_list : Columns.C128.coefficients=List.ofFn CoefficientMatrix.column128 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C128
