import Coulomb8.Columns.C101
import Coulomb8.CoefficientMatrix.C12

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C101

theorem coefficient_list : Columns.C101.coefficients=List.ofFn CoefficientMatrix.column101 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C101
