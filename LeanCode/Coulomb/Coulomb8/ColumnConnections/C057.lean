import Coulomb8.Columns.C057
import Coulomb8.CoefficientMatrix.C07

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C057

theorem coefficient_list : Columns.C057.coefficients=List.ofFn CoefficientMatrix.column57 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C057
