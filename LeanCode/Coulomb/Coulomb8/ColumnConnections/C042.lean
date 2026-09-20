import Coulomb8.Columns.C042
import Coulomb8.CoefficientMatrix.C05

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C042

theorem coefficient_list : Columns.C042.coefficients=List.ofFn CoefficientMatrix.column42 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C042
