import Coulomb8.Columns.C139
import Coulomb8.CoefficientMatrix.C17

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C139

theorem coefficient_list : Columns.C139.coefficients=List.ofFn CoefficientMatrix.column139 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C139
