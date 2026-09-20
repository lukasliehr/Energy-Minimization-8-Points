import Lean_Code.ContactFaceLocalModels

set_option maxHeartbeats 1500000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma shortSphereArc_plane (a b : ℝ³) (r : ℝ) :
    inner ℝ (crossVec a b) (shortSphereArc a b r) = 0 := by
  simp only [shortSphereArc, sphereNormalize_inner, inner_add_right, inner_smul_right,
    crossVec_inner_left, crossVec_inner_right, mul_zero, add_zero]

/-- If a face closure contains one interior point of a contact edge, it
contains the entire closed edge. Along the open edge, membership and
nonmembership are both locally persistent; connectedness then propagates
membership, and closedness supplies the endpoints. -/
theorem contact_edge_in_face_of_interior (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c ≤ aInf)
    (hbound : PackingInnerBound c Y) (hirr : PackingIrreducible c Y)
    (base : ℝ³) (v a : Fin 8) (ha : ContactAdj Y c v a)
    (p : ℝ³) (hp : p ∈ contactFaceRegion Y c base) (hpedge : p ∈ OpenContactArc (Y v) (Y a)) :
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
    obtain ⟨n, hn, δ, hδ, hm⟩ := contactFaceRegion_model_at_edge Y c hY hc hcupper hbound hirr
      base (f r) v a ha hrD hre
    have hopen : IsOpen {x : ℝ³ | δ < inner ℝ (f r) x} := isOpen_lt continuous_const (by fun_prop)
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

end SquareAntiprismVerification
