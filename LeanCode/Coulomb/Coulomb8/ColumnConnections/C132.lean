import Coulomb8.Columns.C132
import Coulomb8.CoefficientMatrix.C16

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C132

theorem coefficient_list : Columns.C132.coefficients=List.ofFn CoefficientMatrix.column132 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C132
