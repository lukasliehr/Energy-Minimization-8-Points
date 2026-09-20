import Coulomb8.Columns.C179
import Coulomb8.CoefficientMatrix.C22

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C179

theorem coefficient_list : Columns.C179.coefficients=List.ofFn CoefficientMatrix.column179 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C179
