import Coulomb8.Columns.C048
import Coulomb8.CoefficientMatrix.C06

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C048

theorem coefficient_list : Columns.C048.coefficients=List.ofFn CoefficientMatrix.column48 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C048
