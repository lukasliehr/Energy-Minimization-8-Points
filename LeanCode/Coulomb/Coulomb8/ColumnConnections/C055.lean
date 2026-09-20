import Coulomb8.Columns.C055
import Coulomb8.CoefficientMatrix.C06

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C055

theorem coefficient_list : Columns.C055.coefficients=List.ofFn CoefficientMatrix.column55 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C055
