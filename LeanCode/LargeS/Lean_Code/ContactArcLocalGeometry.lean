import Lean_Code.ContactGraphTrace

set_option maxHeartbeats 1500000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma crossVec_cross_right (x y z : ℝ³) :
    crossVec x (crossVec y z) = inner ℝ x z • y - inner ℝ x y • z := by
  ext i
  fin_cases i <;> simp [crossVec, inner_coordinate_sum, Fin.sum_univ_succ] <;> ring

lemma crossVec_cross_left (x y z : ℝ³) :
    crossVec (crossVec x y) z = inner ℝ x z • y - inner ℝ y z • x := by
  ext i
  fin_cases i <;> simp [crossVec, inner_coordinate_sum, Fin.sum_univ_succ] <;> ring

def contactEdgeCoordinateA (a b : ℝ³) (c : ℝ) (x : ℝ³) : ℝ :=
  (inner ℝ a x - c * inner ℝ b x) / (1 - c ^ 2)

def contactEdgeCoordinateB (a b : ℝ³) (c : ℝ) (x : ℝ³) : ℝ :=
  (inner ℝ b x - c * inner ℝ a x) / (1 - c ^ 2)

lemma contact_coplanar_representation (a b x : ℝ³) (c : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hab : inner ℝ a b = c) (hx : inner ℝ (crossVec a b) x = 0) :
    x = contactEdgeCoordinateA a b c x • a + contactEdgeCoordinateB a b c x • b := by
  have hden : 1 - c ^ 2 ≠ 0 := by nlinarith [hc.1, hc.2]
  have hba : inner ℝ b a = c := (real_inner_comm a b).trans hab
  have hh := triple_cramer a b (crossVec a b) x
  have hnn : inner ℝ (crossVec a b) (crossVec a b) = 1 - c ^ 2 := by
    rw [cross_inner_cross, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, ha, hb, hab, hba]
    ring
  have hbny : inner ℝ (crossVec b (crossVec a b)) x = inner ℝ a x - c * inner ℝ b x := by
    rw [crossVec_cross_right]
    simp [inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq, hb, hba]
  have hnay : inner ℝ (crossVec (crossVec a b) a) x = inner ℝ b x - c * inner ℝ a x := by
    rw [crossVec_cross_left]
    simp [inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq, ha, hba]
  rw [hnn, hbny, hnay, hx, zero_smul, add_zero] at hh
  have hh' := congrArg (fun y : ℝ³ => (1 - c ^ 2)⁻¹ • y) hh
  simpa [contactEdgeCoordinateA, contactEdgeCoordinateB, smul_add, smul_smul,
    hden, div_eq_mul_inv, mul_comm] using hh'

lemma closedShortSphereArc_mem_of_positive_combination (a b x : ℝ³)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hsum : 0 < A + B)
    (hx : ‖x‖ = 1) (hrep : x = A • a + B • b) : x ∈ closedShortSphereArc a b := by
  let r := B / (A + B)
  have hr : r ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hB hsum.le, (div_le_one hsum).mpr (by linarith)⟩
  have h1 : 1 - r = (A + B)⁻¹ * A := by dsimp [r]; field_simp; ring
  have h2 : r = (A + B)⁻¹ * B := by dsimp [r]; ring
  have hcomb : (1 - r) • a + r • b = (A + B)⁻¹ • x := by
    rw [hrep, smul_add, smul_smul, smul_smul, h1, h2]
  refine ⟨r, hr, ?_⟩
  unfold shortSphereArc
  rw [hcomb]
  exact sphereNormalize_pos_smul_unit x hx _ (inv_pos.mpr hsum)

lemma contact_edge_coordinates_positive (a b x : ℝ³) (c : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hab : inner ℝ a b = c) (hx : x ∈ OpenContactArc a b) :
    0 < contactEdgeCoordinateA a b c x ∧ 0 < contactEdgeCoordinateB a b c x := by
  obtain ⟨r, hr0, hr1, hrep⟩ := hx
  let v := (1 - r) • a + r • b
  have hden : 1 - c ^ 2 ≠ 0 := by nlinarith [hc.1, hc.2]
  have hanti := contact_endpoints_nonantipodal a b hb c hc.1 hab
  have hv : 0 < ‖v‖ := norm_pos_iff.mpr (shortSphereArc_combination_ne_zero a b ha hb hanti r ⟨hr0.le, hr1.le⟩)
  have hba : inner ℝ b a = c := (real_inner_comm a b).trans hab
  have hia : inner ℝ a x = ‖v‖⁻¹ * ((1 - r) + r * c) := by
    rw [hrep]
    simp only [inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq, ha, hab, one_pow, mul_one]
    rfl
  have hib : inner ℝ b x = ‖v‖⁻¹ * ((1 - r) * c + r) := by
    rw [hrep]
    simp only [inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq, hb, hba, one_pow, mul_one]
    rfl
  have hA : contactEdgeCoordinateA a b c x = ‖v‖⁻¹ * (1 - r) := by
    unfold contactEdgeCoordinateA
    rw [hia, hib]
    field_simp
    ring
  have hB : contactEdgeCoordinateB a b c x = ‖v‖⁻¹ * r := by
    unfold contactEdgeCoordinateB
    rw [hia, hib]
    field_simp
    ring
  rw [hA, hB]
  exact ⟨mul_pos (inv_pos.mpr hv) (sub_pos.mpr hr1), mul_pos (inv_pos.mpr hv) hr0⟩

/-- At an interior point, a contact arc is locally exactly its supporting
great circle on the unit sphere. Endpoint exclusion is encoded by strict
positivity of the two continuous edge coordinates. -/
theorem contact_arc_local_plane (a b x : ℝ³) (c : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hab : inner ℝ a b = c) (hx : x ∈ OpenContactArc a b) :
    ∃ U : Set ℝ³, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, y ∈ closedShortSphereArc a b ↔
        ‖y‖ = 1 ∧ inner ℝ (crossVec a b) y = 0 := by
  let U : Set ℝ³ := {y | 0 < contactEdgeCoordinateA a b c y ∧ 0 < contactEdgeCoordinateB a b c y}
  have hAo : IsOpen {y | 0 < contactEdgeCoordinateA a b c y} :=
    isOpen_lt continuous_const (by unfold contactEdgeCoordinateA; fun_prop)
  have hBo : IsOpen {y | 0 < contactEdgeCoordinateB a b c y} :=
    isOpen_lt continuous_const (by unfold contactEdgeCoordinateB; fun_prop)
  have hU : IsOpen U := hAo.inter hBo
  refine ⟨U, hU, contact_edge_coordinates_positive a b x c ha hb hc hab hx, ?_⟩
  intro y hy
  constructor
  · rintro ⟨r, hr, rfl⟩
    refine ⟨shortSphereArc_unit a b ha hb (contact_endpoints_nonantipodal a b hb c hc.1 hab) r hr, ?_⟩
    simp only [shortSphereArc, sphereNormalize_inner, inner_add_right, inner_smul_right,
      crossVec_inner_left, crossVec_inner_right, mul_zero, add_zero]
  · intro hyplane
    exact closedShortSphereArc_mem_of_positive_combination a b y _ _ hy.1.le hy.2.le
      (add_pos hy.1 hy.2) hyplane.1 (contact_coplanar_representation a b y c ha hb hc hab hyplane.2)

end SquareAntiprismVerification
