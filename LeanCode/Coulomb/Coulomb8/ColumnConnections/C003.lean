import Coulomb8.Columns.C003
import Coulomb8.CoefficientMatrix.C00

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C003

theorem coefficient_list : Columns.C003.coefficients=List.ofFn CoefficientMatrix.column3 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C003
