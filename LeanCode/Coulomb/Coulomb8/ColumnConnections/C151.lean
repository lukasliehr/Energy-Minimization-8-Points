import Coulomb8.Columns.C151
import Coulomb8.CoefficientMatrix.C18

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C151

theorem coefficient_list : Columns.C151.coefficients=List.ofFn CoefficientMatrix.column151 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C151
