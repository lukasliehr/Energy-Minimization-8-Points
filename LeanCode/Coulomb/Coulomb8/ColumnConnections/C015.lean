import Coulomb8.Columns.C015
import Coulomb8.CoefficientMatrix.C01

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C015

theorem coefficient_list : Columns.C015.coefficients=List.ofFn CoefficientMatrix.column15 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C015
