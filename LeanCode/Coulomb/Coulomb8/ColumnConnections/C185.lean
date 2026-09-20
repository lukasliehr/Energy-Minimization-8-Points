import Coulomb8.Columns.C185
import Coulomb8.CoefficientMatrix.C23

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C185

theorem coefficient_list : Columns.C185.coefficients=List.ofFn CoefficientMatrix.column185 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C185
