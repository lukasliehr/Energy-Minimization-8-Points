import Coulomb8.Columns.C068
import Coulomb8.CoefficientMatrix.C08

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C068

theorem coefficient_list : Columns.C068.coefficients=List.ofFn CoefficientMatrix.column68 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C068
