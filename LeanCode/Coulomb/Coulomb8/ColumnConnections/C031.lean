import Coulomb8.Columns.C031
import Coulomb8.CoefficientMatrix.C03

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C031

theorem coefficient_list : Columns.C031.coefficients=List.ofFn CoefficientMatrix.column31 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C031
