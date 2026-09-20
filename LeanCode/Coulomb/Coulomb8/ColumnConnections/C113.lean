import Coulomb8.Columns.C113
import Coulomb8.CoefficientMatrix.C14

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C113

theorem coefficient_list : Columns.C113.coefficients=List.ofFn CoefficientMatrix.column113 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C113
