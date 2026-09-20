import Coulomb8.Columns.C014
import Coulomb8.CoefficientMatrix.C01

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C014

theorem coefficient_list : Columns.C014.coefficients=List.ofFn CoefficientMatrix.column14 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C014
