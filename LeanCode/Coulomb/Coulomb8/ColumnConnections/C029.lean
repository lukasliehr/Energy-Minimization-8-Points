import Coulomb8.Columns.C029
import Coulomb8.CoefficientMatrix.C03

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C029

theorem coefficient_list : Columns.C029.coefficients=List.ofFn CoefficientMatrix.column29 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C029
