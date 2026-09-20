import Lean_Code.Parameter

/-!
The declarations from Sections 3--4 will be added here in dependency order.
The initial scaffold deliberately contains no geometric black box.
-/

open Real

noncomputable section

namespace SquareAntiprismVerification

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- A point of the sphere and an ordered eight-tuple of sphere points.  The
ambient tuple type is compact; unlike `Configuration8`, it also contains
collision limits. -/
abbrev SpherePoint := {x : ℝ³ // x ∈ unitSphere}
abbrev SphereTuple := Fin 8 → SpherePoint

lemma spherePoint_isCompact : IsCompact (unitSphere : Set ℝ³) := by
  have hset : unitSphere = Metric.sphere (0 : ℝ³) 1 := by
    ext x
    simp [unitSphere]
  rw [hset]
  exact isCompact_sphere 0 1

noncomputable instance : CompactSpace SpherePoint :=
  isCompact_iff_compactSpace.mp spherePoint_isCompact

def toSphereTuple (Y : Fin 8 → ℝ³) (hY : ∀ i, Y i ∈ unitSphere) : SphereTuple :=
  fun i => ⟨Y i, hY i⟩

def fromSphereTuple (Y : SphereTuple) : Fin 8 → ℝ³ := fun i => Y i

@[simp] lemma from_toSphereTuple (Y : Fin 8 → ℝ³)
    (hY : ∀ i, Y i ∈ unitSphere) :
    fromSphereTuple (toSphereTuple Y hY) = Y := rfl

lemma fromSphereTuple_sphere (Y : SphereTuple) :
    ∀ i, fromSphereTuple Y i ∈ unitSphere := fun i => (Y i).property

@[simp] lemma to_fromSphereTuple (Y : SphereTuple) :
    toSphereTuple (fromSphereTuple Y) (fromSphereTuple_sphere Y) = Y := by
  funext i
  exact Subtype.ext rfl

def OrbitNeighborhood (U : Set SphereTuple) : Prop :=
  ∀ Y : Fin 8 → ℝ³, ∀ hY : ∀ i, Y i ∈ unitSphere,
    Congruent Y P → toSphereTuple Y hY ∈ U

end SquareAntiprismVerification
