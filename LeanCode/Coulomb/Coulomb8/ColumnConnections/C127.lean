import Coulomb8.Columns.C127
import Coulomb8.CoefficientMatrix.C15

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C127

theorem coefficient_list : Columns.C127.coefficients=List.ofFn CoefficientMatrix.column127 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C127
