import Coulomb8.Columns.C087
import Coulomb8.CoefficientMatrix.C10

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C087

theorem coefficient_list : Columns.C087.coefficients=List.ofFn CoefficientMatrix.column87 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C087
