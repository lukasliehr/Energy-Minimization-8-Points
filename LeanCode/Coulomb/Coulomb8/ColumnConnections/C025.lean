import Coulomb8.Columns.C025
import Coulomb8.CoefficientMatrix.C03

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C025

theorem coefficient_list : Columns.C025.coefficients=List.ofFn CoefficientMatrix.column25 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C025
