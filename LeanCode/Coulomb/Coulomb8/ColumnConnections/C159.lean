import Coulomb8.Columns.C159
import Coulomb8.CoefficientMatrix.C19

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C159

theorem coefficient_list : Columns.C159.coefficients=List.ofFn CoefficientMatrix.column159 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C159
