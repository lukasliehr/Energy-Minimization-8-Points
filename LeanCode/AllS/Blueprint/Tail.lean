import Blueprint.Target

/-! Typed tail contracts. Definitions name obligations; they do not prove them.
The final theorem is only the definitional match to the parent's TailSpec.
-/
noncomputable section
open Real
open scoped BigOperators
namespace Blueprint.Thomson.Tail

def packingHeight : ℝ := (2 * √2 - 1) / 7
def tau : ℝ := 2 * (1 - packingHeight)
def gap : ℝ := 33 / 1000
def radius : ℝ := 3 / 10
def contraction : ℝ := 77 / 100
def ceiling : ℝ := 1547 / 100
def pStart : ℝ := 97 / 2

def squaredDistance (Y : Fin 8 → Point) (i j : Fin 8) : ℝ := ‖Y i - Y j‖ ^ 2
def squaredEnergy (p : ℝ) (Y : Fin 8 → Point) : ℝ :=
  ∑ i : Fin 8, ∑ j : Fin 8 with i < j, (squaredDistance Y i j) ^ (-p)

def Stationary (p : ℝ) (Y : Fin 8 → Point) : Prop :=
  ∀ γ : ℝ → Fin 8 → Point, γ 0 = Y →
    (∀ i, DifferentiableAt ℝ (fun t => γ t i) 0) →
    (∀ᶠ t in nhds (0 : ℝ), ∀ i, ‖γ t i‖ = 1) →
    HasDerivAt (fun t => squaredEnergy p (γ t)) 0 0

def forceFactor (m : ℝ) : ℝ :=
  (4 + 8 * √((1 - √(1 - m / 4)) / 2)) / √(1 - m / 4) - 3

def ForceSpec : Prop :=
  ∀ (p m : ℝ) (Y : Fin 8 → Point), IsConfiguration Y → 0 < p →
    Stationary p Y → 0 < m → m ≤ 29 / 20 →
    (∀ i j, i ≠ j → m ≤ squaredDistance Y i j) →
    (∃ i j, i ≠ j ∧ squaredDistance Y i j = m) →
    forceFactor m * m ^ (-p) ≤ squaredEnergy p Y

def ForceEndpointSpec : Prop :=
  ∀ (p m m₀ : ℝ) (Y : Fin 8 → Point), IsConfiguration Y → 3 / 2 ≤ p →
    Stationary p Y → 0 < m → m ≤ m₀ → m₀ ≤ 29 / 20 →
    (∀ i j, i ≠ j → m ≤ squaredDistance Y i j) →
    (∃ i j, i ≠ j ∧ squaredDistance Y i j = m) →
    forceFactor m₀ * m₀ ^ (-p) ≤ squaredEnergy p Y

/-- Explicit reference reordering: paper even/odd layers versus target blocks. -/
def cyclicIndex : Fin 8 → Fin 8 := ![0, 4, 1, 5, 2, 6, 3, 7]
def packingReference (i : Fin 8) : Point := X packingHeight (cyclicIndex i)

def productObjective (Y : Fin 8 → Point) (U : Point ≃ₗᵢ[ℝ] Point)
    (σ : Equiv.Perm (Fin 8)) : ℝ :=
  ∏ i : Fin 8, max (inner ℝ (packingReference i) (U (Y (σ i)))) 0

def ProductBoundarySpec : Prop :=
  ∀ (Y : Fin 8 → Point), (∀ i, ‖Y i‖ = 1) →
    (∀ i j, i ≠ j → inner ℝ (Y i) (Y j) ≤ packingHeight + gap / 2) →
    ¬ ∃ (U : Point ≃ₗᵢ[ℝ] Point) (σ : Equiv.Perm (Fin 8)),
      productObjective Y U σ = 239 / 250 ∧
      ∀ (V : Point ≃ₗᵢ[ℝ] Point) (σ' : Equiv.Perm (Fin 8)),
        productObjective Y V σ' ≤ productObjective Y U σ

/-- Existence of a close alignment avoids an infimum convention in the contract. -/
def LocalizationSpec : Prop :=
  ∀ Y : Fin 8 → Point, (∀ i, ‖Y i‖ = 1) →
    (∀ i j, i ≠ j → tau - gap ≤ squaredDistance Y i j) →
    ∃ (U : Point ≃ₗᵢ[ℝ] Point) (σ : Equiv.Perm (Fin 8)),
      (∑ i : Fin 8, ‖U (Y (σ i)) - packingReference i‖ ^ 2) < radius ^ 2

abbrev TangentCoordinates := EuclideanSpace ℝ (Fin 8 × Fin 2)

/-- The final quantified target, without an existential unspecified cutoff. -/
def TailRangeSpec : Prop :=
  ∀ s : ℝ, 97 ≤ s → ∀ a : ℝ,
    a ∈ Set.Ioo (0 : ℝ) 1 → F s a = 0 → IsUniqueMinimizer s (X a)

theorem tailRangeSpec_iff_target : TailRangeSpec ↔ Blueprint.TailSpec := Iff.rfl

end Blueprint.Thomson.Tail
