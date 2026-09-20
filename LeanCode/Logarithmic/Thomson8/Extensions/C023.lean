import Thomson8.ExtensionChecker

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Thomson8.Extensions

theorem check_C023 : ∀ a b c : Fin 4, extensionCheck 0 2 3 a b c := by
  decide +kernel

#print axioms check_C023

end Thomson8.Extensions
