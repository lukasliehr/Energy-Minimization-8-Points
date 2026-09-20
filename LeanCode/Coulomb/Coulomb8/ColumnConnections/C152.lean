import Coulomb8.Columns.C152
import Coulomb8.CoefficientMatrix.C19

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C152

theorem coefficient_list : Columns.C152.coefficients=List.ofFn CoefficientMatrix.column152 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C152
