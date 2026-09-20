import Coulomb8.Columns.C027
import Coulomb8.CoefficientMatrix.C03

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C027

theorem coefficient_list : Columns.C027.coefficients=List.ofFn CoefficientMatrix.column27 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C027
