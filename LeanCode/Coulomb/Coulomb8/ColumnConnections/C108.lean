import Coulomb8.Columns.C108
import Coulomb8.CoefficientMatrix.C13

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C108

theorem coefficient_list : Columns.C108.coefficients=List.ofFn CoefficientMatrix.column108 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C108
