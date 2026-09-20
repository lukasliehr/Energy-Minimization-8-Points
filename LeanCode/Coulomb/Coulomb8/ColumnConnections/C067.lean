import Coulomb8.Columns.C067
import Coulomb8.CoefficientMatrix.C08

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C067

theorem coefficient_list : Columns.C067.coefficients=List.ofFn CoefficientMatrix.column67 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C067
