import Coulomb8.Columns.C071
import Coulomb8.CoefficientMatrix.C08

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C071

theorem coefficient_list : Columns.C071.coefficients=List.ofFn CoefficientMatrix.column71 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C071
