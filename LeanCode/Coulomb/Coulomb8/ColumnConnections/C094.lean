import Coulomb8.Columns.C094
import Coulomb8.CoefficientMatrix.C11

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C094

theorem coefficient_list : Columns.C094.coefficients=List.ofFn CoefficientMatrix.column94 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C094
