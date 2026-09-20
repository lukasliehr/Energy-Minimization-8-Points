import Coulomb8.Columns.C157
import Coulomb8.CoefficientMatrix.C19

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C157

theorem coefficient_list : Columns.C157.coefficients=List.ofFn CoefficientMatrix.column157 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C157
