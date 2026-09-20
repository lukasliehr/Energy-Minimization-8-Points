import Coulomb8.Columns.C075
import Coulomb8.CoefficientMatrix.C09

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C075

theorem coefficient_list : Columns.C075.coefficients=List.ofFn CoefficientMatrix.column75 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C075
