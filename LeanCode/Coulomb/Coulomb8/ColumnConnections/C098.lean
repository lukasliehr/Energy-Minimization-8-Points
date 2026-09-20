import Coulomb8.Columns.C098
import Coulomb8.CoefficientMatrix.C12

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C098

theorem coefficient_list : Columns.C098.coefficients=List.ofFn CoefficientMatrix.column98 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C098
