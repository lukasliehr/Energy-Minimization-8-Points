import AllS.Units.N_GI.N_face_convex.N_short_arc_closed
import Lean_Code.InitialSupportingFace

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem boundary_support_edge_propagation (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c < 3/10)
    (hbound : PackingInnerBound c Y) (hirr : PackingIrreducible c Y)
    (base : Point) (v a : Fin 8) (ha : ContactAdj Y c v a)
    (p : Point) (hp : p ∈ contactFaceRegion Y c base) (hpedge : p ∈ OpenContactArc (Y v) (Y a)) :
    ∀ r ∈ Set.Icc (0 : ℝ) 1, shortSphereArc (Y v) (Y a) r ∈ contactFaceRegion Y c base := by
  let D := contactFaceRegion Y c base
  let f := shortSphereArc (Y v) (Y a)
  let R : Set ℝ := f ⁻¹' D
  have hD : IsClosed D := (contactFaceRegion_compact Y c base).isClosed
  have hanti := contact_endpoints_nonantipodal (Y v) (Y a) (hY.1 a) c hc.1 ha.2
  have hcont (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) : ContinuousAt f r :=
    shortSphereArc_continuousAt _ _ (hY.1 v) (hY.1 a) hanti r hr
  have hunit (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) : ‖f r‖ = 1 :=
    shortSphereArc_unit _ _ (hY.1 v) (hY.1 a) hanti r hr
  have hloc (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) 1) (hrD : r ∈ R) : r ∈ interior R := by
    have hre : f r ∈ OpenContactArc (Y v) (Y a) := ⟨r, hr.1, hr.2, rfl⟩
    obtain ⟨n, hn, δ, hδ, hm⟩ := face_models_edge_model Y c hY hc hcupper hbound hirr
      base (f r) v a ha hrD hre
    have hopen : IsOpen {x : Point | δ < inner ℝ (f r) x} := isOpen_lt continuous_const (by fun_prop)
    have hrN : δ < inner ℝ (f r) (f r) := by
      simpa [real_inner_self_eq_norm_sq, hunit r ⟨hr.1.le, hr.2.le⟩] using hδ.2
    have hevent : ∀ᶠ s in nhds r, δ < inner ℝ (f r) (f s) :=
      (hcont r ⟨hr.1.le, hr.2.le⟩) (hopen.mem_nhds hrN)
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hevent, isOpen_Ioo.mem_nhds hr] with s hs hsI
    apply (hm (f s) hs).mpr
    refine ⟨hunit s ⟨hsI.1.le, hsI.2.le⟩, ?_⟩
    have hplane : inner ℝ (crossVec (Y v) (Y a)) (f s) = 0 := shortSphereArc_plane (Y v) (Y a) s
    rcases hn with rfl | rfl
    · exact hplane.ge
    · simpa only [inner_neg_left, hplane, neg_zero] using (le_refl (0 : ℝ))
  have hnot (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) 1) (hrD : r ∉ R) : r ∈ interior Rᶜ := by
    apply mem_interior_iff_mem_nhds.mpr
    exact (hcont r ⟨hr.1.le, hr.2.le⟩) (hD.isOpen_compl.mem_nhds hrD)
  obtain ⟨r₀, hr₀0, hr₀1, hr₀p⟩ := hpedge
  have hr₀D : r₀ ∈ R := by
    have heq : f r₀ = p := hr₀p.symm
    change f r₀ ∈ D
    rw [heq]
    exact hp
  have hall (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) 1) : r ∈ R := by
    by_contra hrD
    have hcover : Set.Ioo (0 : ℝ) 1 ⊆ interior R ∪ interior Rᶜ := by
      intro s hs
      by_cases hsD : s ∈ R
      · exact Or.inl (hloc s hs hsD)
      · exact Or.inr (hnot s hs hsD)
    obtain ⟨s, hs, hsR, hsnot⟩ := isPreconnected_Ioo (interior R) (interior Rᶜ)
      isOpen_interior isOpen_interior hcover
      ⟨r₀, ⟨hr₀0, hr₀1⟩, hloc r₀ ⟨hr₀0, hr₀1⟩ hr₀D⟩ ⟨r, hr, hnot r hr hrD⟩
    exact (interior_subset hsnot) (interior_subset hsR)
  have hzero : f 0 ∈ D := by
    by_contra hn
    have hnear : {s | f s ∈ Dᶜ} ∈ nhds (0 : ℝ) :=
      (hcont 0 ⟨le_rfl, zero_le_one⟩) (hD.isOpen_compl.mem_nhds hn)
    obtain ⟨s, hs, hs0, hs1⟩ := exists_small_positive_in_neighborhood _ hnear 1 zero_lt_one
    exact hs (hall s ⟨hs0, hs1⟩)
  have hone : f 1 ∈ D := by
    by_contra hn
    have hfc : ContinuousAt (fun s : ℝ => f (1 - s)) 0 :=
      ContinuousAt.comp (f := fun s : ℝ => 1 - s) (g := f) (x := (0 : ℝ))
        (by simpa using hcont 1 ⟨zero_le_one, le_rfl⟩) (by fun_prop)
    have hnear : {s | f (1 - s) ∈ Dᶜ} ∈ nhds (0 : ℝ) :=
      hfc (by simpa only [sub_zero] using hD.isOpen_compl.mem_nhds hn)
    obtain ⟨s, hs, hs0, hs1⟩ := exists_small_positive_in_neighborhood _ hnear 1 zero_lt_one
    exact hs (hall (1 - s) ⟨by linarith, by linarith⟩)
  intro r hr
  by_cases hr0 : r = 0
  · subst r; exact hzero
  by_cases hr1 : r = 1
  · subst r; exact hone
  · exact hall r ⟨lt_of_le_of_ne hr.1 (Ne.symm hr0), lt_of_le_of_ne hr.2 hr1⟩

#print axioms boundary_support_edge_propagation

theorem boundary_support_initial_left_face (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c < 3/10)
    (hbound : PackingInnerBound c Y) (hirr : PackingIrreducible c Y) (d : ContactDart Y c) :
    ∃ base : Point, ‖base‖ = 1 ∧ base ∉ contactGraphTrace Y c ∧
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
  obtain ⟨U₂, hU₂, hp₂, hsep⟩ := sector_separation_edge_sides Y c hY hc hcupper hbound hirr v a hadj p hpu hpedge
  obtain ⟨δ, hδ, hcap⟩ := sphericalOpenCap_small p hpu (U₁ ∩ U₂) (hU₁.inter hU₂) ⟨hp₁, hp₂⟩
  let W : Set Point := {y | δ < inner ℝ p y}
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
  have hin (y : Point) (hy : y ∈ sphericalOpenCap p δ)
      (hy₁ : 0 < inner ℝ n y) (hy₂ : 0 < inner ℝ n y) : y ∈ (contactGraphTrace Y c)ᶜ := by
    intro h
    exact hy₁.ne' (((hplane y (hcap hy).1).mp h).2)
  have hs (y : Point) (hy : y ∈ sphericalOpenCap p δ)
      (hyN : inner ℝ n y < 0 ∨ inner ℝ n y < 0) :
      ¬JoinedIn (openSphericalRegion (contactGraphTrace Y c)ᶜ) base y :=
    hsep base (hcap hbcap).2 y (hcap hy).2 hbpos (hyN.elim id id)
  have hm := component_wedge_local_model (contactGraphTrace Y c)ᶜ base p n n n δ hδ.1 hnn hnn
    hin base hbF hbcap hbpos hbpos hs
  let D := contactFaceRegion Y c base
  have hpD : p ∈ D := (hm p hpW).mpr ⟨hpu, hnp.ge, hnp.ge⟩
  have hglobal : ∀ x ∈ D, 0 ≤ inner ℝ n x := global_halfspace_of_open_local_support D
    (closed_spherical_component_unit _ base)
    (face_convex_short_arc_closed Y c hY hc hcupper hbound hirr base hbu hbG)
    p n hpD hnp W hW hpW (fun x hx hxW => ((hm x hxW).mp hx).2.1)
  refine ⟨base, hbu, hbG, ?_, hglobal⟩
  exact boundary_support_edge_propagation Y c hY hc hcupper hbound hirr base v a hadj p hpD hpedge

#print axioms boundary_support_initial_left_face

end Blueprint.Thomson.Tail.Implementation
