import Coulomb8.Columns.C058
import Coulomb8.CoefficientMatrix.C07

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C058

theorem coefficient_list : Columns.C058.coefficients=List.ofFn CoefficientMatrix.column58 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C058
