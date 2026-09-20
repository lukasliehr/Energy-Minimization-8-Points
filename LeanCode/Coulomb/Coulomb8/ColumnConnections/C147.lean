import Coulomb8.Columns.C147
import Coulomb8.CoefficientMatrix.C18

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ColumnConnections.C147

theorem coefficient_list : Columns.C147.coefficients=List.ofFn CoefficientMatrix.column147 :=
  by decide +kernel

end Coulomb8.ColumnConnections.C147
