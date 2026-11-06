import Blueprint.Tail

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Tail.Implementation

def coordinateReorder : TangentCoordinates →ₗ[ℝ] ((Fin 8 → ℝ) × (Fin 8 → ℝ)) where
  toFun q := (fun i => q (i,0), fun i => q (i,1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem upstream_bridge_euclidean_coordinates (q : TangentCoordinates) :
    ‖q‖^2 = ∑i : Fin 8, (q (i,0)^2 + q (i,1)^2) := by
  simp [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- This only states the Euclidean coordinate identity; the target product
space of `coordinateReorder` has a different ambient norm. -/
theorem coordinateReorder_norm_identity (q : TangentCoordinates) :
    ‖q‖^2 = ∑i : Fin 8, ((coordinateReorder q).1 i^2 + (coordinateReorder q).2 i^2) :=
  upstream_bridge_euclidean_coordinates q

#print axioms upstream_bridge_euclidean_coordinates
end Blueprint.Thomson.Tail.Implementation
