import Coulomb8.Columns.C064
import Coulomb8.CoefficientMatrix.C08

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C064

theorem coefficient_list : Columns.C064.coefficients=List.ofFn CoefficientMatrix.column64 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C064
