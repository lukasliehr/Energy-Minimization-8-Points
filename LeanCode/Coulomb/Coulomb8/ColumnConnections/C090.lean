import Coulomb8.Columns.C090
import Coulomb8.CoefficientMatrix.C11

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C090

theorem coefficient_list : Columns.C090.coefficients=List.ofFn CoefficientMatrix.column90 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C090
