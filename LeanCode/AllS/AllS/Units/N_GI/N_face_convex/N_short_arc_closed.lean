import AllS.Units.N_GI.N_face_models.N_local_polyhedral

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem face_convex_short_arc_closed (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c < 3/10)
    (hbound : PackingInnerBound c Y) (hirr : PackingIrreducible c Y)
    (base : Point) (hbase : ‖base‖ = 1) (hbaseG : base ∉ contactGraphTrace Y c) :
    ShortArcClosed (contactFaceRegion Y c base) := by
  letI : PreconnectedSpace (contactFaceRegion Y c base) :=
    isPreconnected_iff_preconnectedSpace.mp (contactFaceRegion_preconnected Y c base hbase hbaseG)
  exact shortArcClosed_of_compact_local_models (contactFaceRegion_compact Y c base)
    (face_models_local_polyhedral Y c hY hc hcupper hbound hirr base)
    (contactFaceRegion_dense_interior Y c hY hc.1 base)

#print axioms face_convex_short_arc_closed

end Blueprint.Thomson.Tail.Implementation
