import Coulomb8.Columns.C181
import Coulomb8.CoefficientMatrix.C22

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C181

theorem coefficient_list : Columns.C181.coefficients=List.ofFn CoefficientMatrix.column181 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C181
