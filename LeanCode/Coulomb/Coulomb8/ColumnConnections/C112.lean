import Coulomb8.Columns.C112
import Coulomb8.CoefficientMatrix.C14

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C112

theorem coefficient_list : Columns.C112.coefficients=List.ofFn CoefficientMatrix.column112 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C112
