import Coulomb8.Columns.C081
import Coulomb8.CoefficientMatrix.C10

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C081

theorem coefficient_list : Columns.C081.coefficients=List.ofFn CoefficientMatrix.column81 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C081
