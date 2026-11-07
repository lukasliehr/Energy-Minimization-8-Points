import AllS.Units.N_G.N_setup
import Lean_Code.ContactFaceLocalModels

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem face_models_off_graph_model (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : 0 < c) (a x : Point)
    (hx : x ∈ contactFaceRegion Y c a) (hxoff : x ∉ contactGraphTrace Y c) :
    ∃ W : Set Point, IsOpen W ∧ x ∈ W ∧
      ∀ y ∈ W, y ∈ contactFaceRegion Y c a ↔ ‖y‖ = 1 :=
  closed_spherical_component_model_off_graph _
    (contactGraphTrace_compact Y c hY hc).isClosed.isOpen_compl a x hx hxoff

#print axioms face_models_off_graph_model

end Blueprint.Thomson.Tail.Implementation
