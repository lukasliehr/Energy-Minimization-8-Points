import Coulomb8.Columns.C178
import Coulomb8.CoefficientMatrix.C22

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C178

theorem coefficient_list : Columns.C178.coefficients=List.ofFn CoefficientMatrix.column178 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C178
