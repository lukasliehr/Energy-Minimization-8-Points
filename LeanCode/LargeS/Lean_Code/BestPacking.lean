import Lean_Code.PackingConstants
import Lean_Code.PackingEndgame
import Lean_Code.PackingReduction
import Lean_Code.PackingMaximum
import Lean_Code.ContactGeometryGlobal
import Lean_Code.ContactCovering
import Lean_Code.ContactDirections
import Lean_Code.RhombusConcavity
import Lean_Code.VertexConcavity
import Lean_Code.RhombusScalar
import Lean_Code.AreaSummation
import Lean_Code.OrbitClosure
import Lean_Code.ContactSeparation
import Lean_Code.RhombusBounds
import Lean_Code.EqualityReconstruction
import Lean_Code.GlobalPackingAssembly
import Lean_Code.ArcEmbedding
import Lean_Code.ContactComponents
import Lean_Code.RotationSystem
import Lean_Code.ContactBoundary
import Lean_Code.SphericalPolygon
import Lean_Code.TangentAngles
import Lean_Code.PolygonExcess
import Lean_Code.BoundaryPolygons
import Lean_Code.ComponentHemisphere
import Lean_Code.BoundaryPartition
import Lean_Code.ContactFaceRegions
import Lean_Code.BoundaryCoverage
import Lean_Code.PermutationFixedSpace
import Lean_Code.ContactEulerBound
import Lean_Code.BoundarySupportAssembly
import Lean_Code.ShortBoundaryCycles
import Lean_Code.ContactQuadrilateral
import Lean_Code.BoundaryFaceSupport

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Rigidity direction of the paper's eight-point best-packing theorem.
Actual complementary face regions supply strict support of their directed
boundaries. The checked contact-tiling and equality reconstruction then
give congruence to the optimal square antiprism. -/
theorem eight_point_best_packing_rigidity
    (Y : Fin 8 → ℝ³) (hY : ∀ i, Y i ∈ unitSphere)
    (hsep : ∀ i j, i ≠ j → tau ≤ ‖Y i - Y j‖ ^ 2) :
    Congruent Y P :=
  packing_rigidity_interface_of_boundary_support irreducible_boundary_support Y hY hsep

end SquareAntiprismVerification
