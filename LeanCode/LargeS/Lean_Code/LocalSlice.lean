import Lean_Code.BestPacking
import Lean_Code.Infinitesimal
import Lean_Code.ContactRankBound
import Lean_Code.LocalChart
import Lean_Code.PackingLoss
import Lean_Code.ChartBounds
import Lean_Code.StrictConvexity
import Lean_Code.ChartInverse
import Lean_Code.SliceCovering
import Lean_Code.LocalClassification

/-!
The explicit slice, rank certificate, positive stress, and linear packing
loss from Section 5 will live here.
-/

open Real

noncomputable section

namespace SquareAntiprismVerification

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The combined local-slice, linear-loss, and shrinking-ball convexity
conclusion of Sections 5--6.  Its neighborhood is independent of `p`; only
the exponent threshold remains. -/
theorem eventual_local_sublevel_classification :
    ∃ U : Set SphereTuple, IsOpen U ∧ OrbitNeighborhood U ∧
      ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p ≥ p₀,
        ∀ Y : Fin 8 → ℝ³, ∀ hY : IsConfiguration Y,
          toSphereTuple Y hY.1 ∈ U → E (2 * p) Y ≤ E (2 * p) P →
            E (2 * p) Y ≥ E (2 * p) (X (aStar (2 * p))) ∧
            (E (2 * p) Y = E (2 * p) (X (aStar (2 * p))) ↔
              Congruent Y (X (aStar (2 * p)))) :=
  eventual_local_sublevel_classification_proved

end SquareAntiprismVerification
