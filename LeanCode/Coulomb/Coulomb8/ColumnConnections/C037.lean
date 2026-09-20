import Coulomb8.Columns.C037
import Coulomb8.CoefficientMatrix.C04

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C037

theorem coefficient_list : Columns.C037.coefficients=List.ofFn CoefficientMatrix.column37 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C037
