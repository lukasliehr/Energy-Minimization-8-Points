import Coulomb8.Columns.C041
import Coulomb8.CoefficientMatrix.C05

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C041

theorem coefficient_list : Columns.C041.coefficients=List.ofFn CoefficientMatrix.column41 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C041
