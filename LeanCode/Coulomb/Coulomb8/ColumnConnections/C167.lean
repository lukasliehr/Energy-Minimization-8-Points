import Coulomb8.Columns.C167
import Coulomb8.CoefficientMatrix.C20

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C167

theorem coefficient_list : Columns.C167.coefficients=List.ofFn CoefficientMatrix.column167 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C167
