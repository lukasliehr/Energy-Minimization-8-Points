import Coulomb8.Columns.C177
import Coulomb8.CoefficientMatrix.C22

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C177

theorem coefficient_list : Columns.C177.coefficients=List.ofFn CoefficientMatrix.column177 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C177
