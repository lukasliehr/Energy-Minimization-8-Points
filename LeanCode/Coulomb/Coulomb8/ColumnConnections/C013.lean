import Coulomb8.Columns.C013
import Coulomb8.CoefficientMatrix.C01

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C013

theorem coefficient_list : Columns.C013.coefficients=List.ofFn CoefficientMatrix.column13 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C013
