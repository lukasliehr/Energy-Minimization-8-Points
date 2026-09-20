import Coulomb8.Columns.C053
import Coulomb8.CoefficientMatrix.C06

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C053

theorem coefficient_list : Columns.C053.coefficients=List.ofFn CoefficientMatrix.column53 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C053
