import AllS.Units.N_GI.N_product_gauge.N_chord_stationarity

noncomputable section
open SquareAntiprismVerification (crossVec inverseSphereChart)
namespace Blueprint.Thomson.Tail.Implementation

theorem cross_projection (p y : Point) : crossVec p (inverseSphereChart p y)=crossVec p y := by
  ext k
  fin_cases k <;> simp [crossVec,inverseSphereChart] <;> ring

theorem inverseCoordinates_mem_rotationSlice (Y : Fin 8 → Point)
    (halign : (∑ i, crossVec (packingReference i) (Y i))=0) : inverseCoordinates Y ∈ rotationSlice := by
  change rotationVector (inverseCoordinates Y)=0
  simpa only [rotationVector,inverseCoordinates_tangent,cross_projection] using halign

theorem nearest_chart_orthogonal_slice (Y : Fin 8 → Point) (hY : ∀ i, ‖Y i‖=1)
    (hmin : IsChordAligned Y) : inverseCoordinates Y ∈ rotationSlice :=
  inverseCoordinates_mem_rotationSlice Y (chord_alignment_cross_zero Y hY hmin)

#check nearest_chart_orthogonal_slice
#print axioms nearest_chart_orthogonal_slice
end Blueprint.Thomson.Tail.Implementation
