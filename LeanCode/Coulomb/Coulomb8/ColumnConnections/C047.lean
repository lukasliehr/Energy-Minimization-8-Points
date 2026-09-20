import Coulomb8.Columns.C047
import Coulomb8.CoefficientMatrix.C05

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C047

theorem coefficient_list : Columns.C047.coefficients=List.ofFn CoefficientMatrix.column47 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C047
