import Coulomb8.Columns.C012
import Coulomb8.CoefficientMatrix.C01

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C012

theorem coefficient_list : Columns.C012.coefficients=List.ofFn CoefficientMatrix.column12 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C012
