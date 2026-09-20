import Coulomb8.Columns.C061
import Coulomb8.CoefficientMatrix.C07

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C061

theorem coefficient_list : Columns.C061.coefficients=List.ofFn CoefficientMatrix.column61 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C061
