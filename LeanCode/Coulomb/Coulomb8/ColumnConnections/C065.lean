import Coulomb8.Columns.C065
import Coulomb8.CoefficientMatrix.C08

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C065

theorem coefficient_list : Columns.C065.coefficients=List.ofFn CoefficientMatrix.column65 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C065
