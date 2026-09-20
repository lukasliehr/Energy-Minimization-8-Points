import Coulomb8.Columns.C078
import Coulomb8.CoefficientMatrix.C09

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C078

theorem coefficient_list : Columns.C078.coefficients=List.ofFn CoefficientMatrix.column78 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C078
