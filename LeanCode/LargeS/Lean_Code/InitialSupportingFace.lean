import Lean_Code.FaceDartPropagation

set_option maxHeartbeats 1500000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Choose a genuine complementary face on the left of an oriented
contact edge. Its local halfspace model, global convexity, and edge
propagation establish the initial boundary-walk invariant. -/
theorem initial_supporting_face (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c ≤ aInf)
    (hbound : PackingInnerBound c Y) (hirr : PackingIrreducible c Y) (d : ContactDart Y c) :
    ∃ base : ℝ³, ‖base‖ = 1 ∧ base ∉ contactGraphTrace Y c ∧
      FaceSupportsDart Y c (contactFaceRegion Y c base) d := by
  let v := d.1
  let a := d.2.val
  let n := crossVec (Y v) (Y a)
  let p := shortSphereArc (Y v) (Y a) (1 / 2)
  have hadj : ContactAdj Y c v a := ⟨d.2.property.1.symm, d.2.property.2⟩
  have hpedge : p ∈ OpenContactArc (Y v) (Y a) := ⟨1 / 2, by norm_num, by norm_num, rfl⟩
  have hanti := contact_endpoints_nonantipodal (Y v) (Y a) (hY.1 a) c hc.1 hadj.2
  have hpu : ‖p‖ = 1 := shortSphereArc_unit _ _ (hY.1 v) (hY.1 a) hanti (1 / 2) (by norm_num)
  have hnp : inner ℝ n p = 0 := shortSphereArc_plane (Y v) (Y a) (1 / 2)
  have hn : n ≠ 0 := norm_pos_iff.mp (contact_cross_norm_pos (Y v) (Y a) c (hY.1 v) (hY.1 a) hc hadj.2)
  have hnn : 0 < inner ℝ n n := by rw [real_inner_self_eq_norm_sq]; exact sq_pos_of_pos (norm_pos_iff.mpr hn)
  obtain ⟨U₁, hU₁, hp₁, hplane⟩ := contactGraphTrace_local_plane Y c hY hc hbound v a hadj p hpedge
  obtain ⟨U₂, hU₂, hp₂, hsep⟩ := contact_edge_sides_not_joined Y c hY hc hcupper hbound hirr v a hadj p hpu hpedge
  obtain ⟨δ, hδ, hcap⟩ := sphericalOpenCap_small p hpu (U₁ ∩ U₂) (hU₁.inter hU₂) ⟨hp₁, hp₂⟩
  let W : Set ℝ³ := {y | δ < inner ℝ p y}
  have hW : IsOpen W := isOpen_lt continuous_const (by fun_prop)
  have hpW : p ∈ W := by simpa [W, real_inner_self_eq_norm_sq, hpu] using hδ.2
  obtain ⟨base, hbW, hbu, hbN⟩ := unit_nearby_strict_normals (fun _ : Unit => n) p n hpu
    (fun _ => hnp) (fun _ => hnn) W hW hpW
  have hbcap : base ∈ sphericalOpenCap p δ := ⟨hbu, hbW⟩
  have hbpos : 0 < inner ℝ n base := hbN ()
  have hbG : base ∉ contactGraphTrace Y c := by
    intro h
    have hh := ((hplane base (hcap hbcap).1).mp h).2
    exact hbpos.ne' hh
  have hbF : base ∈ pathComponentIn (openSphericalRegion (contactGraphTrace Y c)ᶜ) base :=
    mem_pathComponentIn_self ⟨hbu, hbG⟩
  have hin (y : ℝ³) (hy : y ∈ sphericalOpenCap p δ)
      (hy₁ : 0 < inner ℝ n y) (hy₂ : 0 < inner ℝ n y) : y ∈ (contactGraphTrace Y c)ᶜ := by
    intro h
    exact hy₁.ne' (((hplane y (hcap hy).1).mp h).2)
  have hs (y : ℝ³) (hy : y ∈ sphericalOpenCap p δ)
      (hyN : inner ℝ n y < 0 ∨ inner ℝ n y < 0) :
      ¬JoinedIn (openSphericalRegion (contactGraphTrace Y c)ᶜ) base y :=
    hsep base (hcap hbcap).2 y (hcap hy).2 hbpos (hyN.elim id id)
  have hm := component_wedge_local_model (contactGraphTrace Y c)ᶜ base p n n n δ hδ.1 hnn hnn
    hin base hbF hbcap hbpos hbpos hs
  let D := contactFaceRegion Y c base
  have hpD : p ∈ D := (hm p hpW).mpr ⟨hpu, hnp.ge, hnp.ge⟩
  have hglobal : ∀ x ∈ D, 0 ≤ inner ℝ n x := global_halfspace_of_open_local_support D
    (closed_spherical_component_unit _ base)
    (contactFaceRegion_shortArcClosed Y c hY hc hcupper hbound hirr base hbu hbG)
    p n hpD hnp W hW hpW (fun x hx hxW => ((hm x hxW).mp hx).2.1)
  refine ⟨base, hbu, hbG, ?_, hglobal⟩
  exact contact_edge_in_face_of_interior Y c hY hc hcupper hbound hirr base v a hadj p hpD hpedge

end SquareAntiprismVerification
