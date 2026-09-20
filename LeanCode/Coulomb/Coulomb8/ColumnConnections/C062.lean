import Coulomb8.Columns.C062
import Coulomb8.CoefficientMatrix.C07

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C062

theorem coefficient_list : Columns.C062.coefficients=List.ofFn CoefficientMatrix.column62 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C062
