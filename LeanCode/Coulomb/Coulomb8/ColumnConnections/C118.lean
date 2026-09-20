import Coulomb8.Columns.C118
import Coulomb8.CoefficientMatrix.C14

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C118

theorem coefficient_list : Columns.C118.coefficients=List.ofFn CoefficientMatrix.column118 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C118
