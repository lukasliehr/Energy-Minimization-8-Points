import Coulomb8.Columns.C123
import Coulomb8.CoefficientMatrix.C15

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C123

theorem coefficient_list : Columns.C123.coefficients=List.ofFn CoefficientMatrix.column123 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C123
