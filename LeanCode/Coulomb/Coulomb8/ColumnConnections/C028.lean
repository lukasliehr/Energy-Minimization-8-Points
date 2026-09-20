import Coulomb8.Columns.C028
import Coulomb8.CoefficientMatrix.C03

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C028

theorem coefficient_list : Columns.C028.coefficients=List.ofFn CoefficientMatrix.column28 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C028
