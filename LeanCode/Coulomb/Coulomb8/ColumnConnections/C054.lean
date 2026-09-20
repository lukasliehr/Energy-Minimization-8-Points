import Coulomb8.Columns.C054
import Coulomb8.CoefficientMatrix.C06

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C054

theorem coefficient_list : Columns.C054.coefficients=List.ofFn CoefficientMatrix.column54 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C054
