import Coulomb8.Columns.C180
import Coulomb8.CoefficientMatrix.C22

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C180

theorem coefficient_list : Columns.C180.coefficients=List.ofFn CoefficientMatrix.column180 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C180
