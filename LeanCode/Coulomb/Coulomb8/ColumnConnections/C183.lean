import Coulomb8.Columns.C183
import Coulomb8.CoefficientMatrix.C22

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C183

theorem coefficient_list : Columns.C183.coefficients=List.ofFn CoefficientMatrix.column183 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C183
