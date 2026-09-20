import Coulomb8.ExtensionChecker

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.ExtensionChecks

theorem base53 (r s w : Fin 4) : extensionCheck 3 1 1 r s w := by
  fin_cases r <;> fin_cases s <;> fin_cases w <;> decide +kernel

end Coulomb8.ExtensionChecks
