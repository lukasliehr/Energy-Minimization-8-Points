import Coulomb8.Columns.C165
import Coulomb8.CoefficientMatrix.C20

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C165

theorem coefficient_list : Columns.C165.coefficients=List.ofFn CoefficientMatrix.column165 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C165
