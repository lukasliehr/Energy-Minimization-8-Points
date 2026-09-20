import Coulomb8.Columns.C103
import Coulomb8.CoefficientMatrix.C12

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C103

theorem coefficient_list : Columns.C103.coefficients=List.ofFn CoefficientMatrix.column103 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C103
