import Coulomb8.Columns.C176
import Coulomb8.CoefficientMatrix.C22

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C176

theorem coefficient_list : Columns.C176.coefficients=List.ofFn CoefficientMatrix.column176 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C176
