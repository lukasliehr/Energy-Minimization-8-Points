import Coulomb8.Columns.C010
import Coulomb8.CoefficientMatrix.C01

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C010

theorem coefficient_list : Columns.C010.coefficients=List.ofFn CoefficientMatrix.column10 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C010
