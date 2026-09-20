import Coulomb8.Columns.C156
import Coulomb8.CoefficientMatrix.C19

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C156

theorem coefficient_list : Columns.C156.coefficients=List.ofFn CoefficientMatrix.column156 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C156
