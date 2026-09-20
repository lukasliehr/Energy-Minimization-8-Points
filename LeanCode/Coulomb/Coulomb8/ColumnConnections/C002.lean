import Coulomb8.Columns.C002
import Coulomb8.CoefficientMatrix.C00

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C002

theorem coefficient_list : Columns.C002.coefficients=List.ofFn CoefficientMatrix.column2 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C002
