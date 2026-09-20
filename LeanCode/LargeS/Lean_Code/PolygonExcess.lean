import Lean_Code.SphericalFan

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma sphereVertexAngle_comm (p q r : ℝ³) : sphereVertexAngle p q r = sphereVertexAngle p r q :=
  sphereAngle_comm _ _

lemma fin_sum_successive_differences {n : ℕ} (f : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, (f i.succ - f i.castSucc) = f (Fin.last n) - f 0 := by
  have hleft := Fin.sum_univ_succ f
  have hright := Fin.sum_univ_castSucc f
  rw [Finset.sum_sub_distrib]
  linarith

namespace StrictSphericalPolygon

variable {n : ℕ}

def fanCornerA (Q : StrictSphericalPolygon n) (i : Fin (n + 1)) : ℝ :=
  sphereVertexAngle (Q.vertex 0) (Q.vertex i.castSucc.succ) (Q.vertex i.succ.succ)

def fanCornerB (Q : StrictSphericalPolygon n) (i : Fin (n + 1)) : ℝ :=
  sphereVertexAngle (Q.vertex i.castSucc.succ) (Q.vertex i.succ.succ) (Q.vertex 0)

def fanCornerC (Q : StrictSphericalPolygon n) (i : Fin (n + 1)) : ℝ :=
  sphereVertexAngle (Q.vertex i.succ.succ) (Q.vertex 0) (Q.vertex i.castSucc.succ)

lemma fan_triangle_positive (Q : StrictSphericalPolygon n) (i : Fin (n + 1)) :
    Real.pi < Q.fanCornerA i + Q.fanCornerB i + Q.fanCornerC i := by
  have htriple := Q.support i.castSucc.succ 0 (Fin.succ_ne_zero i.castSucc).symm
    (by rw [fan_successor_index]; exact (Fin.succ_ne_zero i.succ).symm)
  rw [fan_successor_index, triple_cyclic, triple_cyclic] at htriple
  exact spherical_triangle_excess_positive _ _ _ (Q.unit 0) (Q.unit _) (Q.unit _) htriple.ne'

lemma fanCornerA_difference (Q : StrictSphericalPolygon n) (i : Fin (n + 1)) :
    Q.fanCornerA i = Q.fanAngle i.succ - Q.fanAngle i.castSucc := by
  by_cases hi : i = 0
  · subst i
    change Q.fanAngle (Fin.succ 0) = Q.fanAngle (Fin.succ 0) - Q.fanAngle 0
    rw [Q.fanAngle_zero, sub_zero]
  · have hleft : i.castSucc ≠ 0 := by
      intro h
      apply hi
      apply Fin.ext
      exact congrArg (fun k : Fin (n + 2) => k.val) h
    have hside := Q.support i.castSucc.succ 0 (Fin.succ_ne_zero i.castSucc).symm
      (by rw [fan_successor_index]; exact (Fin.succ_ne_zero i.succ).symm)
    rw [fan_successor_index, triple_cyclic, triple_cyclic] at hside
    have hadd := sphereVertexAngle_add (Q.vertex 0) (Q.vertex 1)
      (Q.vertex i.castSucc.succ) (Q.vertex i.succ.succ)
      (Q.unit 0) (Q.unit 1) (Q.unit _) (Q.unit _)
      (Q.fan_support i.castSucc hleft) hside (Q.fan_support i.succ (Fin.succ_ne_zero i))
    change Q.fanAngle i.castSucc + Q.fanCornerA i = Q.fanAngle i.succ at hadd
    linarith

lemma sum_fanCornerA (Q : StrictSphericalPolygon n) : ∑ i, Q.fanCornerA i = Q.angle 0 := by
  simp only [Q.fanCornerA_difference]
  rw [fin_sum_successive_differences, Q.fanAngle_zero, sub_zero]
  have hlast : (0 : Fin (n + 3)) - 1 = Fin.last (n + 2) :=
    (eq_sub_iff_add_eq.mpr (Fin.last_add_one (n + 2))).symm
  simp only [fanAngle, angle, hlast]
  rfl

lemma fanCornerB_first (Q : StrictSphericalPolygon n) : Q.fanCornerB 0 = Q.angle 1 := by
  have hnext : (1 : Fin (n + 3)) + 1 = 2 := by
    exact fan_successor_index (0 : Fin (n + 1))
  simp only [fanCornerB, angle, hnext, sub_self]
  rfl

lemma fanCornerC_last (Q : StrictSphericalPolygon n) :
    Q.fanCornerC (Fin.last n) = Q.angle (Fin.last (n + 2)) := by
  have hprev : (Fin.last (n + 2) : Fin (n + 3)) - 1 = (Fin.last n).castSucc.succ := by
    apply (eq_sub_iff_add_eq.mpr ?_).symm
    exact fan_successor_index (Fin.last n)
  simp only [fanCornerC, angle, Fin.last_add_one, hprev]
  rfl

lemma fan_middle_corner (Q : StrictSphericalPolygon n) (i : Fin n) :
    Q.fanCornerB i.succ + Q.fanCornerC i.castSucc = Q.angle i.castSucc.succ.succ := by
  let a : Fin (n + 3) := i.castSucc.castSucc.succ
  let b : Fin (n + 3) := i.castSucc.succ.succ
  let d : Fin (n + 3) := i.succ.succ.succ
  have hab : a + 1 = b := fan_successor_index i.castSucc
  have hbd : b + 1 = d := fan_successor_index i.succ
  have ha0 : a ≠ 0 := Fin.succ_ne_zero _
  have hb0 : b ≠ 0 := Fin.succ_ne_zero _
  have hd0 : d ≠ 0 := Fin.succ_ne_zero _
  have habne : a ≠ b := by rw [← hab]; exact (cyclic_one_ne n a).symm
  have hadne : a ≠ d := by rw [← hbd, ← hab]; exact (cyclic_two_ne n a).symm
  have hba := Q.support a 0 ha0.symm (by rw [hab]; exact hb0.symm)
  rw [hab, triple_cyclic] at hba
  have hbd0 := Q.support b 0 hb0.symm (by rw [hbd]; exact hd0.symm)
  rw [hbd] at hbd0
  have hbda := Q.support b a habne (by rw [hbd]; exact hadne)
  rw [hbd] at hbda
  have hadd := sphereVertexAngle_add (Q.vertex b) (Q.vertex d) (Q.vertex 0) (Q.vertex a)
    (Q.unit b) (Q.unit d) (Q.unit 0) (Q.unit a) hbd0 hba hbda
  have hbprev : b - 1 = a := (eq_sub_iff_add_eq.mpr hab).symm
  change sphereVertexAngle (Q.vertex b) (Q.vertex d) (Q.vertex 0) +
    sphereVertexAngle (Q.vertex b) (Q.vertex 0) (Q.vertex a) = Q.angle b
  rw [angle, hbd, hbprev]
  exact hadd

theorem sum_fan_corners (Q : StrictSphericalPolygon n) :
    ∑ i, (Q.fanCornerA i + Q.fanCornerB i + Q.fanCornerC i) = ∑ i, Q.angle i := by
  have hA := Q.sum_fanCornerA
  have hB := Fin.sum_univ_succ Q.fanCornerB
  have hC := Fin.sum_univ_castSucc Q.fanCornerC
  rw [Q.fanCornerB_first] at hB
  rw [Q.fanCornerC_last] at hC
  have hmiddle : ∑ i : Fin n, (Q.fanCornerB i.succ + Q.fanCornerC i.castSucc) =
      ∑ i : Fin n, Q.angle i.castSucc.succ.succ := by
    apply Finset.sum_congr rfl
    intro i _
    exact Q.fan_middle_corner i
  rw [Finset.sum_add_distrib] at hmiddle
  have hP1 := Fin.sum_univ_succ Q.angle
  have hP2 := Fin.sum_univ_succ (fun i : Fin (n + 2) => Q.angle i.succ)
  have hP3 := Fin.sum_univ_castSucc (fun i : Fin (n + 1) => Q.angle i.succ.succ)
  change ∑ i : Fin (n + 2), Q.angle i.succ = Q.angle 1 +
    ∑ i : Fin (n + 1), Q.angle i.succ.succ at hP2
  change ∑ i : Fin (n + 1), Q.angle i.succ.succ =
    (∑ i : Fin n, Q.angle i.castSucc.succ.succ) + Q.angle (Fin.last (n + 2)) at hP3
  simp only [Finset.sum_add_distrib]
  linarith

/-- Positive spherical excess, obtained by adding the actual angles of
the fan triangles. No spherical area measure is assumed here. -/
theorem positive_excess (Q : StrictSphericalPolygon n) :
    ((n : ℝ) + 1) * Real.pi < ∑ i, Q.angle i := by
  have h : (∑ _i : Fin (n + 1), Real.pi) <
      ∑ i, (Q.fanCornerA i + Q.fanCornerB i + Q.fanCornerC i) :=
    Finset.sum_lt_sum (fun i _ => (Q.fan_triangle_positive i).le)
      ⟨0, Finset.mem_univ _, Q.fan_triangle_positive 0⟩
  simpa only [Q.sum_fan_corners, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] using h

theorem perimeter_lt_two_pi (Q : StrictSphericalPolygon n) : Q.perimeter < 2 * Real.pi :=
  Q.perimeter_lt_of_polar_excess Q.polar.positive_excess

end StrictSphericalPolygon

lemma packing_edge_angle_gt (c : ℝ) (hc : 0 < c) (hcupper : c ≤ aInf) :
    2 * Real.pi / 5 < Real.arccos c := by
  have ha : aInf < 2 / 7 := by nlinarith [aInf_quadratic, aInf_mem_Ioo.1]
  have hs : (15 : ℝ) / 7 < Real.sqrt 5 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg (5 : ℝ)]
  have hcos : 2 / 7 < Real.cos (2 * Real.pi / 5) := by
    rw [cos_two_pi_fifths]
    linarith
  have hc1 : c < 1 := hcupper.trans_lt aInf_mem_Ioo.2
  have hcosc := Real.cos_arccos (show -1 ≤ c by linarith) hc1.le
  by_contra h
  have hle : Real.arccos c ≤ 2 * Real.pi / 5 := le_of_not_gt h
  have hanti := Real.strictAntiOn_cos.antitoneOn
    (show Real.arccos c ∈ Set.Icc (0 : ℝ) Real.pi from
      ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩)
    (show 2 * Real.pi / 5 ∈ Set.Icc (0 : ℝ) Real.pi from
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩) hle
  rw [hcosc] at hanti
  linarith

theorem contact_polygon_three_or_four {n : ℕ} (Q : StrictSphericalPolygon n) (c : ℝ)
    (hc : 0 < c) (hcupper : c ≤ aInf)
    (hcontact : ∀ i, inner ℝ (Q.vertex i) (Q.vertex (i + 1)) = c) :
    n + 3 = 3 ∨ n + 3 = 4 := by
  have hperim := Q.perimeter_lt_two_pi
  simp only [StrictSphericalPolygon.perimeter, sphereAngle, hcontact,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hperim
  have hangle := packing_edge_angle_gt c hc hcupper
  have hn : ((n + 3 : ℕ) : ℝ) < 5 := by
    have hapos : 0 < Real.arccos c := by linarith [Real.pi_pos]
    nlinarith
  have hn' : n + 3 < 5 := by exact_mod_cast hn
  omega

end SquareAntiprismVerification
