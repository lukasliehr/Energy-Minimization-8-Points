import Coulomb8.Columns.C044
import Coulomb8.CoefficientMatrix.C05

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C044

theorem coefficient_list : Columns.C044.coefficients=List.ofFn CoefficientMatrix.column44 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C044
