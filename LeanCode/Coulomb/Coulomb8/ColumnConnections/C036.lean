import Coulomb8.Columns.C036
import Coulomb8.CoefficientMatrix.C04

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C036

theorem coefficient_list : Columns.C036.coefficients=List.ofFn CoefficientMatrix.column36 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C036
