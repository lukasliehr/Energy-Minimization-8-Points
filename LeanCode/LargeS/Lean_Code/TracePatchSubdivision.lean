import Lean_Code.GreatCircleTrace

set_option maxHeartbeats 1000000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

def PatchArcChain.reendpoint {ι : Type*} {patch : ι → Set ℝ³} {a b a' b' : ℝ³}
    (p : PatchArcChain patch a b) (ha : a = a') (hb : b = b') : PatchArcChain patch a' b' :=
  ha ▸ hb ▸ p

lemma PatchArcChain.reendpoint_length {ι : Type*} {patch : ι → Set ℝ³} {a b a' b' : ℝ³}
    (p : PatchArcChain patch a b) (ha : a = a') (hb : b = b') :
    (p.reendpoint ha hb).length = p.length := by
  cases ha
  cases hb
  rfl

/-- A continuous trace with an angular length bound can be replaced by an
actual finite patch chain without increasing that bound. The supremum
argument supplies a finite subdivision without choosing a uniform mesh. -/
theorem patch_chain_of_trace {D : Set ℝ³} (P : CompactArcPatchCover D)
    (f : ℝ → ℝ³) (hf : Continuous f) (L : ℝ) (hL : 0 ≤ L)
    (hunit : ‖f 0‖ = 1) (hinside : ∀ u ∈ Set.Icc (0 : ℝ) L, f u ∈ D)
    (hangle : ∀ u ∈ Set.Icc (0 : ℝ) L, ∀ v ∈ Set.Icc (0 : ℝ) L,
      u ≤ v → sphereAngle (f u) (f v) ≤ v - u) :
    ∃ q : PatchArcChain P.patch (f 0) (f L), q.length ≤ L := by
  classical
  let S : Set ℝ := {u | u ∈ Set.Icc (0 : ℝ) L ∧
    ∃ q : PatchArcChain P.patch (f 0) (f u), q.length ≤ u}
  have hzero : 0 ∈ S := ⟨⟨le_rfl, hL⟩, .point hunit, le_rfl⟩
  have hne : S.Nonempty := ⟨0, hzero⟩
  have hbounded : BddAbove S := ⟨L, fun u hu => hu.1.2⟩
  let b := sSup S
  have hb0 : 0 ≤ b := le_csSup hbounded hzero
  have hbL : b ≤ L := csSup_le hne (fun u hu => hu.1.2)
  have hbI : b ∈ Set.Icc (0 : ℝ) L := ⟨hb0, hbL⟩
  obtain ⟨i, U, hU, hpatch⟩ := P.local_cover_ambient (f b) (hinside b hbI)
  have hevent : ∀ᶠ u in nhds b, f u ∈ U := hf.continuousAt hU
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hevent
  have hbpatch : f b ∈ P.patch i := hpatch (f b) (hinside b hbI) (mem_of_mem_nhds hU)
  have hnear : ∃ u ∈ S, b - δ < u := by
    by_contra hn
    push_neg at hn
    have hh : b ≤ b - δ := csSup_le hne hn
    linarith
  obtain ⟨u, huS, hnear⟩ := hnear
  have hub : u ≤ b := le_csSup hbounded huS
  have huU : f u ∈ U := hball (by
    change dist u b < δ
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hub)]
    linarith)
  have hupatch : f u ∈ P.patch i := hpatch (f u) (hinside u huS.1) huU
  obtain ⟨q, hq⟩ := huS.2
  let qb : PatchArcChain P.patch (f 0) (f b) := .tail q i (f b) hupatch hbpatch
  have hqb : qb.length ≤ b := by
    have hh := hangle u huS.1 b hbI hub
    change q.length + sphereAngle (f u) (f b) ≤ b
    linarith
  have hbS : b ∈ S := ⟨hbI, qb, hqb⟩
  have hbEq : b = L := by
    by_contra hn
    have hlt : b < L := lt_of_le_of_ne hbL hn
    let ε := min δ (L - b) / 2
    have hε : 0 < ε := half_pos (lt_min hδ (sub_pos.mpr hlt))
    have hεδ : ε < δ := by
      dsimp [ε]
      have := min_le_left δ (L - b)
      linarith
    have hεL : ε < L - b := by
      dsimp [ε]
      have := min_le_right δ (L - b)
      linarith
    have hcI : b + ε ∈ Set.Icc (0 : ℝ) L := ⟨by linarith, by linarith⟩
    have hcU : f (b + ε) ∈ U := hball (by
      change dist (b + ε) b < δ
      simpa [Real.dist_eq, abs_of_pos hε] using hεδ)
    have hcpatch := hpatch (f (b + ε)) (hinside _ hcI) hcU
    let qc : PatchArcChain P.patch (f 0) (f (b + ε)) :=
      .tail qb i (f (b + ε)) hbpatch hcpatch
    have hqc : qc.length ≤ b + ε := by
      have hh := hangle b hbI (b + ε) hcI (by linarith)
      change qb.length + sphereAngle (f b) (f (b + ε)) ≤ b + ε
      linarith
    have hcS : b + ε ∈ S := ⟨hcI, qc, hqc⟩
    have hh : b + ε ≤ b := le_csSup hbounded hcS
    linarith
  exact hbEq ▸ (show ∃ q : PatchArcChain P.patch (f 0) (f b), q.length ≤ b from hbS.2)

lemma greatCirclePoint_angle_le_abs (m t : ℝ³) (hm : ‖m‖ = 1) (ht : ‖t‖ = 1)
    (horth : inner ℝ m t = 0) (u v : ℝ) :
    sphereAngle (greatCirclePoint m t u) (greatCirclePoint m t v) ≤ |u - v| := by
  by_cases h : |u - v| ≤ Real.pi
  · exact (greatCirclePoint_angle m t hm ht horth u v h).le
  · exact (sphereAngle_range _ _).2.trans (le_of_not_ge h)

/-- Every great-circle interval contained in the region has a competing
finite patch chain of at most its parameter length, including long arcs. -/
theorem great_circle_patch_chain {D : Set ℝ³} (P : CompactArcPatchCover D)
    (m t : ℝ³) (hm : ‖m‖ = 1) (ht : ‖t‖ = 1) (horth : inner ℝ m t = 0)
    (s L : ℝ) (hL : 0 ≤ L)
    (hinside : ∀ u ∈ Set.Icc (0 : ℝ) L, greatCirclePoint m t (s + u) ∈ D) :
    ∃ q : PatchArcChain P.patch (greatCirclePoint m t s) (greatCirclePoint m t (s + L)),
      q.length ≤ L := by
  have hf : Continuous (fun u : ℝ => greatCirclePoint m t (s + u)) :=
    (greatCirclePoint_continuous m t).comp (continuous_const.add continuous_id)
  have h := patch_chain_of_trace P (fun u => greatCirclePoint m t (s + u)) hf L hL
    (greatCirclePoint_unit m t hm ht horth _) hinside (by
      intro u hu v hv huv
      have hh := greatCirclePoint_angle_le_abs m t hm ht horth (s + u) (s + v)
      have heq : |s + u - (s + v)| = v - u := by
        rw [show s + u - (s + v) = u - v by ring, abs_of_nonpos (sub_nonpos.mpr huv)]
        ring
      simpa only [heq] using hh)
  obtain ⟨q, hq⟩ := h
  exact ⟨q.reendpoint (by rw [add_zero]) rfl, by simpa only [PatchArcChain.reendpoint_length] using hq⟩

end SquareAntiprismVerification
