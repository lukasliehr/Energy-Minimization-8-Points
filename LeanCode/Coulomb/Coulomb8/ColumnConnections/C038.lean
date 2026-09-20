import Coulomb8.Columns.C038
import Coulomb8.CoefficientMatrix.C04

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C038

theorem coefficient_list : Columns.C038.coefficients=List.ofFn CoefficientMatrix.column38 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C038
