import Coulomb8.Columns.C007
import Coulomb8.CoefficientMatrix.C00

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C007

theorem coefficient_list : Columns.C007.coefficients=List.ofFn CoefficientMatrix.column7 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C007
