import Coulomb8.Columns.C189
import Coulomb8.CoefficientMatrix.C23

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C189

theorem coefficient_list : Columns.C189.coefficients=List.ofFn CoefficientMatrix.column189 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C189
