import Lean_Code.ShortArcPatchChains

set_option maxHeartbeats 1000000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma shortSphereArc_on_greatCircle (m t : ℝ³) (hm : ‖m‖ = 1) (ht : ‖t‖ = 1)
    (horth : inner ℝ m t = 0) (u v : ℝ) (huv : u < v) (hpi : v - u < Real.pi)
    (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    ∃ w ∈ Set.Icc u v,
      shortSphereArc (greatCirclePoint m t u) (greatCirclePoint m t v) r =
        greatCirclePoint m t w := by
  have hframe : greatCirclePoint (greatCirclePoint m t u) (greatCircleTangent m t u) (v - u) =
      greatCirclePoint m t v := by
    rw [greatCirclePoint_add]
    congr 1
    ring
  obtain ⟨w, hw, heq⟩ := shortSphereArc_greatCircle_parameter
    (greatCirclePoint m t u) (greatCircleTangent m t u)
    (greatCirclePoint_unit m t hm ht horth u) (greatCircleTangent_unit m t hm ht horth u)
    (greatCircleTangent_orthogonal m t hm ht horth u) (v - u)
    ⟨sub_pos.mpr huv, hpi⟩ r hr
  refine ⟨u + w, ⟨by linarith [hw.1], by linarith [hw.2]⟩, ?_⟩
  rw [hframe, greatCirclePoint_add] at heq
  exact heq

/-- The transverse shortcut is a genuine finite patch-chain competitor,
not just an informal comparison of continuous path lengths. -/
theorem great_circle_shorter_patch_chain {D : Set ℝ³} (P : CompactArcPatchCover D)
    (m t : ℝ³) (hm : ‖m‖ = 1) (ht : ‖t‖ = 1) (horth : inner ℝ m t = 0)
    (a : ℝ) (ha : a ∈ Set.Ioo (Real.pi / 2) Real.pi)
    (U : Set ℝ³) (hU : IsOpen U) (hUD : ∀ x ∈ U, ‖x‖ = 1 → x ∈ D)
    (htrace : ∀ u ∈ Set.Icc (-a) a, greatCirclePoint m t u ∈ U) :
    ∃ q : PatchArcChain P.patch (greatCirclePoint m t (-a)) (greatCirclePoint m t a),
      q.length < 2 * a := by
  have ha0 : 0 < a := by linarith [ha.1, Real.pi_pos]
  let V : Set ℝ³ := U ∩ {x | x ≠ 0}
  have hV : IsOpen V := hU.inter (isOpen_ne_fun continuous_id continuous_const)
  have hleft : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      shortSphereArc (greatCirclePoint m t (-a)) m r ∈ V := by
    intro r hr
    obtain ⟨w, hw, heq⟩ := shortSphereArc_on_greatCircle m t hm ht horth (-a) 0
      (by linarith) (by linarith [ha.2]) r hr
    rw [greatCirclePoint_zero] at heq
    rw [heq]
    refine ⟨htrace w ⟨hw.1, by linarith [hw.2]⟩, ?_⟩
    exact norm_ne_zero_iff.mp (by rw [greatCirclePoint_unit m t hm ht horth]; norm_num)
  have hright : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      shortSphereArc (greatCirclePoint m t a) m r ∈ V := by
    intro r hr
    rw [shortSphereArc_reverse]
    obtain ⟨w, hw, heq⟩ := shortSphereArc_on_greatCircle m t hm ht horth 0 a
      ha0 (by simpa using ha.2) (1 - r) ⟨by linarith [hr.2], by linarith [hr.1]⟩
    rw [greatCirclePoint_zero] at heq
    rw [heq]
    refine ⟨htrace w ⟨by linarith [hw.1], hw.2⟩, ?_⟩
    exact norm_ne_zero_iff.mp (by rw [greatCirclePoint_unit m t hm ht horth]; norm_num)
  let n := crossVec m t
  have hn : ‖n‖ = 1 := by
    have hh := crossVec_norm_sq m t
    rw [hm, ht, horth] at hh
    change ‖crossVec m t‖ = 1
    nlinarith [norm_nonneg (crossVec m t)]
  have hmn : inner ℝ m n = 0 := by rw [real_inner_comm]; exact crossVec_inner_left m t
  have htn : inner ℝ t n = 0 := by rw [real_inner_comm]; exact crossVec_inner_right m t
  obtain ⟨z, hz, hl, hr, hshort⟩ := great_circle_shortening_inside_open m t n hm ht hn
    horth hmn htn a ha V hV hleft hright
  have hlanti := shortSphereArc_nonantipodal_of_ne_zero (greatCirclePoint m t (-a)) z
    (hl (1 / 2) (by norm_num)).2
  have hranti := shortSphereArc_nonantipodal_of_ne_zero (greatCirclePoint m t a) z
    (hr (1 / 2) (by norm_num)).2
  have hleftD : ∀ r ∈ Set.Icc (0 : ℝ) 1, shortSphereArc (greatCirclePoint m t (-a)) z r ∈ D := by
    intro r hrr
    exact hUD _ (hl r hrr).1 (shortSphereArc_unit _ _
      (greatCirclePoint_unit m t hm ht horth (-a)) hz hlanti r hrr)
  have hrightD : ∀ r ∈ Set.Icc (0 : ℝ) 1, shortSphereArc z (greatCirclePoint m t a) r ∈ D := by
    intro r hrr
    rw [shortSphereArc_reverse]
    have hrr' : 1 - r ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hrr.2], by linarith [hrr.1]⟩
    exact hUD _ (hr _ hrr').1 (shortSphereArc_unit _ _
      (greatCirclePoint_unit m t hm ht horth a) hz hranti _ hrr')
  obtain ⟨ql, hql⟩ := short_arc_patch_chain P _ z
    (greatCirclePoint_unit m t hm ht horth (-a)) hz hlanti hleftD
  have hranti' : z ≠ -greatCirclePoint m t a := by
    intro hh
    exact hranti (by rw [hh, neg_neg])
  obtain ⟨qr, hqr⟩ := short_arc_patch_chain P z _ hz
    (greatCirclePoint_unit m t hm ht horth a) hranti' hrightD
  refine ⟨ql.trans qr, ?_⟩
  rw [PatchArcChain.trans_length]
  linarith

/-- A minimizing trace whose interior lies in the relative interior of the
region cannot be longer than a semicircle. Prefix, shortcut, and suffix are
all explicit admissible patch chains. -/
theorem shortest_great_circle_length_le_pi_of_interior {D : Set ℝ³} (P : CompactArcPatchCover D)
    {m b : ℝ³} (p : PatchArcChain P.patch m b) (hmin : p.IsShortest)
    (t : ℝ³) (hm : ‖m‖ = 1) (ht : ‖t‖ = 1) (horth : inner ℝ m t = 0)
    (hend : greatCirclePoint m t p.length = b)
    (htrace : ∀ u ∈ Set.Icc (0 : ℝ) p.length, greatCirclePoint m t u ∈ D)
    (U : Set ℝ³) (hU : IsOpen U) (hUD : ∀ x ∈ U, ‖x‖ = 1 → x ∈ D)
    (hinterior : ∀ u ∈ Set.Ioo (0 : ℝ) p.length, greatCirclePoint m t u ∈ U) :
    p.length ≤ Real.pi := by
  by_contra hn
  have hlong : Real.pi < p.length := lt_of_not_ge hn
  let a := (Real.pi / 2 + min Real.pi (p.length / 2)) / 2
  have hminpos : Real.pi / 2 < min Real.pi (p.length / 2) :=
    lt_min (by linarith [Real.pi_pos]) (by linarith)
  have ha0 : Real.pi / 2 < a := by dsimp [a]; linarith
  have ham : a < min Real.pi (p.length / 2) := by dsimp [a]; linarith
  have hapi : a < Real.pi := ham.trans_le (min_le_left _ _)
  have haL : a < p.length / 2 := ham.trans_le (min_le_right _ _)
  have hapos : 0 < a := by linarith [Real.pi_pos]
  let s := p.length / 2
  let M := greatCirclePoint m t s
  let T := greatCircleTangent m t s
  have hM : ‖M‖ = 1 := greatCirclePoint_unit m t hm ht horth s
  have hT : ‖T‖ = 1 := greatCircleTangent_unit m t hm ht horth s
  have hMT : inner ℝ M T = 0 := greatCircleTangent_orthogonal m t hm ht horth s
  obtain ⟨qmid, hmid⟩ := great_circle_shorter_patch_chain P M T hM hT hMT a
    ⟨ha0, hapi⟩ U hU hUD (by
      intro u hu
      change greatCirclePoint (greatCirclePoint m t s) (greatCircleTangent m t s) u ∈ U
      rw [greatCirclePoint_add]
      apply hinterior
      dsimp [s]
      constructor <;> linarith [hu.1, hu.2])
  have hleft0 : 0 ≤ s - a := by dsimp [s]; linarith
  obtain ⟨ql, hql⟩ := great_circle_patch_chain P m t hm ht horth 0 (s - a) hleft0 (by
    intro u hu
    rw [zero_add]
    exact htrace u ⟨hu.1, by dsimp [s] at hu; linarith [hu.2]⟩)
  have hright0 : 0 ≤ p.length - (s + a) := by dsimp [s]; linarith
  obtain ⟨qr, hqr⟩ := great_circle_patch_chain P m t hm ht horth (s + a)
    (p.length - (s + a)) hright0 (by
      intro u hu
      apply htrace
      dsimp [s] at *
      constructor <;> linarith [hu.1, hu.2])
  have hmidleft : greatCirclePoint M T (-a) = greatCirclePoint m t (0 + (s - a)) := by
    change greatCirclePoint (greatCirclePoint m t s) (greatCircleTangent m t s) (-a) = _
    rw [greatCirclePoint_add]
    congr 1
    ring
  have hmidright : greatCirclePoint M T a = greatCirclePoint m t (s + a) :=
    greatCirclePoint_add m t s a
  let mid := qmid.reendpoint hmidleft hmidright
  let q := (ql.trans mid).trans qr
  have hqstart : greatCirclePoint m t 0 = m := greatCirclePoint_zero m t
  have hqend : greatCirclePoint m t (s + a + (p.length - (s + a))) = b := by
    convert hend using 1 <;> congr 1 <;> ring
  have hshort : q.length < p.length := by
    change ((ql.trans mid).trans qr).length < p.length
    simp only [PatchArcChain.trans_length, mid, PatchArcChain.reendpoint_length]
    dsimp [s] at hql hqr
    linarith
  have h := hmin (q.reendpoint hqstart hqend)
  rw [PatchArcChain.reendpoint_length] at h
  linarith

end SquareAntiprismVerification
