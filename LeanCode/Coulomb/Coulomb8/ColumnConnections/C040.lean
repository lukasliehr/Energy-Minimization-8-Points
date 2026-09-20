import Coulomb8.Columns.C040
import Coulomb8.CoefficientMatrix.C05

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C040

theorem coefficient_list : Columns.C040.coefficients=List.ofFn CoefficientMatrix.column40 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C040
