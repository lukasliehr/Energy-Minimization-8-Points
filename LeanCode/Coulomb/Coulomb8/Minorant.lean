import Coulomb8.QuotientPositive
import Coulomb8.MinorantSemantics

namespace Coulomb8

theorem minorant {t : ℝ} (ht : t ∈ Set.Ico (-1 : ℝ) 1) : H t ≤ phi t :=
  minorant_of_quotient_positive gapQuotient_positive ht

theorem minorant_strict {t : ℝ} (ht : t ∈ Set.Ico (-1 : ℝ) 1) (hc : ¬IsContact t) :
    H t < phi t := minorant_strict_of_quotient_positive gapQuotient_positive ht hc

theorem minorant_equality {t : ℝ} (ht : t ∈ Set.Ico (-1 : ℝ) 1) :
    H t = phi t ↔ IsContact t :=
  minorant_equality_of_quotient_positive gapQuotient_positive ht

end Coulomb8

#print axioms Coulomb8.minorant
#print axioms Coulomb8.minorant_equality
