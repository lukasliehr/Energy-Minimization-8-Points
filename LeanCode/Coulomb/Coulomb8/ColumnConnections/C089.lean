import Coulomb8.Columns.C089
import Coulomb8.CoefficientMatrix.C11

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C089

theorem coefficient_list : Columns.C089.coefficients=List.ofFn CoefficientMatrix.column89 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C089
