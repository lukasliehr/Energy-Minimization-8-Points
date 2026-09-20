import Coulomb8.Columns.C102
import Coulomb8.CoefficientMatrix.C12

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C102

theorem coefficient_list : Columns.C102.coefficients=List.ofFn CoefficientMatrix.column102 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C102
