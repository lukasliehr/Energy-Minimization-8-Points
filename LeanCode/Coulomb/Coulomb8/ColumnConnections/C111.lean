import Coulomb8.Columns.C111
import Coulomb8.CoefficientMatrix.C13

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C111

theorem coefficient_list : Columns.C111.coefficients=List.ofFn CoefficientMatrix.column111 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C111
