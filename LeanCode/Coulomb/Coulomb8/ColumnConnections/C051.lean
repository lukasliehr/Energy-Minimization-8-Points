import Coulomb8.Columns.C051
import Coulomb8.CoefficientMatrix.C06

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C051

theorem coefficient_list : Columns.C051.coefficients=List.ofFn CoefficientMatrix.column51 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C051
