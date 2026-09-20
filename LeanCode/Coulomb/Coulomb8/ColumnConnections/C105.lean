import Coulomb8.Columns.C105
import Coulomb8.CoefficientMatrix.C13

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C105

theorem coefficient_list : Columns.C105.coefficients=List.ofFn CoefficientMatrix.column105 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C105
