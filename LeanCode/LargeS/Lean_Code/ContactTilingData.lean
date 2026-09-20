import Lean_Code.FaceIncidence
import Lean_Code.RhombusFace
import Lean_Code.WeakEulerArea

set_option maxHeartbeats 1500000

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Finite contact-face data required by the area argument. Only the Euler
upper bound is an input; exact Euler equality follows from the area argument
in the packing range. This structure does not assert that a decomposition
exists. Its construction from actual boundary cycles remains separate. -/
structure ContactTilingData (Y : Fin 8 → ℝ³) (c : ℝ) where
  triCount : ℕ
  quadCount : ℕ
  tri : Fin triCount → Fin 3 → Fin 8
  quad : Fin quadCount → Fin 4 → Fin 8
  tri_injective : ∀ f, Function.Injective (tri f)
  quad_injective : ∀ f, Function.Injective (quad f)
  tri_contacts : ∀ f i j, i ≠ j → inner ℝ (Y (tri f i)) (Y (tri f j)) = c
  quad_contacts : ∀ f j, inner ℝ (Y (quad f j)) (Y (quad f (j + 1))) = c
  quad_diagonal02 : ∀ f, inner ℝ (Y (quad f 0)) (Y (quad f 2)) < c
  quad_diagonal13 : ∀ f, inner ℝ (Y (quad f 1)) (Y (quad f 3)) < c
  angle_sum : ∀ v : Fin 8,
    (faceCornerCount tri v : ℝ) * Real.arccos (c / (1 + c)) +
      faceIncidentSum quad (fun f j => quadrilateralAngle c (fun k => Y (quad f k)) j) v = 2 * Real.pi
  euler_lower_bound : 12 ≤ triCount + 2 * quadCount

namespace ContactTilingData
variable {Y : Fin 8 → ℝ³} {c : ℝ}

def alpha (_D : ContactTilingData Y c) : ℝ := Real.arccos (c / (1 + c))
def beta (D : ContactTilingData Y c) : ℝ := 2 * Real.pi - 3 * D.alpha
def gamma (D : ContactTilingData Y c) : ℝ := rhombusDelta (1 / c) D.beta
def triangleExcess (D : ContactTilingData Y c) : ℝ := 3 * D.alpha - Real.pi
def angle (D : ContactTilingData Y c) (f : Fin D.quadCount) (j : Fin 4) : ℝ :=
  quadrilateralAngle c (fun k => Y (D.quad f k)) j
def excess (D : ContactTilingData Y c) (f : Fin D.quadCount) : ℝ :=
  quadrilateralExcess c (fun k => Y (D.quad f k))
def triangleTotal (D : ContactTilingData Y c) : ℝ := D.triCount * D.triangleExcess
def quadTotal (D : ContactTilingData Y c) : ℝ := ∑ f, D.excess f
def localArea (D : ContactTilingData Y c) (v : Fin 8) : ℝ :=
  (faceCornerCount D.tri v : ℝ) * D.triangleExcess +
    faceIncidentSum D.quad (fun f _ => D.excess f) v

theorem corner_geometry (D : ContactTilingData Y c) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (f : Fin D.quadCount) (j : Fin 4) :
    D.angle f j ∈ Set.Ioo D.alpha (2 * D.alpha) ∧
      D.excess f = rhombusArea (1 / c) (D.angle f j) := by
  exact quadrilateral_geometry (fun k => Y (D.quad f k)) c (fun k => hY.1 _)
    hc (hY.2.comp (D.quad_injective f)) (D.quad_contacts f)
    (D.quad_diagonal02 f) (D.quad_diagonal13 f) j

theorem total_excess_before_euler (D : ContactTilingData Y c) :
    D.triangleTotal + D.quadTotal = (16 - ((D.triCount : ℝ) + 2 * (D.quadCount : ℝ))) * Real.pi := by
  have hs := congrArg (fun f : Fin 8 → ℝ => ∑ v, f v) (funext D.angle_sum)
  change (∑ v, ((faceCornerCount D.tri v : ℝ) * D.alpha + faceIncidentSum D.quad D.angle v)) = _ at hs
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_faceCornerCount, sum_faceIncidentSum] at hs
  have hquad : (∑ f, ∑ j, D.angle f j) = D.quadTotal + (D.quadCount : ℝ) * (2 * Real.pi) := by
    simp only [angle, quadrilateralAngle_sum]
    simp [quadTotal, excess, Finset.sum_add_distrib]
  rw [hquad] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at hs
  unfold triangleTotal triangleExcess
  nlinarith

theorem sum_localArea (D : ContactTilingData Y c) :
    ∑ v, D.localArea v = 3 * D.triangleTotal + 4 * D.quadTotal := by
  simp only [localArea, Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [sum_faceCornerCount, sum_faceIncidentArea]
  simp only [triangleTotal, quadTotal, Nat.cast_ofNat]
  ring

theorem local_area_reduction (D : ContactTilingData Y c) (hY : IsConfiguration Y)
    (hc : 0 < c) (hcupper : c ≤ aInf) (v : Fin 8) :
    let f := rhombusArea (1 / c) D.beta - 2 * D.triangleExcess
    0 < f ∧
      ((faceCornerCount D.tri v : ℝ) + 2 * (faceCornerCount D.quad v : ℝ)) * D.triangleExcess + f ≤ D.localArea v ∧
      (D.localArea v = ((faceCornerCount D.tri v : ℝ) + 2 * (faceCornerCount D.quad v : ℝ)) * D.triangleExcess + f →
        faceCornerCount D.quad v = 1 ∧ faceCornerCount D.tri v = 3 ∧
          ∀ p ∈ faceCornersAt D.quad v, D.angle p.1 p.2 = D.beta) := by
  classical
  have hcI : c ∈ Set.Ioo (0 : ℝ) 1 := ⟨hc, hcupper.trans_lt aInf_mem_Ioo.2⟩
  have hα := packing_equilateral_angle_range c hc hcupper
  have hαI := equilateral_angle_Ioo c hcI
  let θ : ↥(faceCornersAt D.quad v) → ℝ := fun p => D.angle p.val.1 p.val.2
  have hθ : ∀ p, θ p ∈ Set.Ioo D.alpha (2 * D.alpha) := fun p => (D.corner_geometry hY hcI _ _).1
  have hθclosed : ∀ p, θ p ∈ Set.Icc D.alpha (2 * D.alpha) := fun p => ⟨(hθ p).1.le, (hθ p).2.le⟩
  have hsumθ : (faceCornerCount D.tri v : ℝ) * D.alpha + ∑ p, θ p = 2 * Real.pi := by
    rw [← faceIncidentSum_eq_subtype_sum]
    exact D.angle_sum v
  have hsumA : (∑ p, rhombusArea (1 / c) (θ p)) = faceIncidentSum D.quad (fun f _ => D.excess f) v := by
    rw [faceIncidentSum_eq_subtype_sum]
    apply Finset.sum_congr rfl
    intro p hp
    exact (D.corner_geometry hY hcI _ _).2.symm
  have hends := rhombusArea_endpoints c D.alpha hc hαI hα.2.2
  obtain ⟨hpos, hbound, hequality⟩ := one_vertex_area_reduction (rhombusArea (1 / c)) D.alpha
    (2 * D.triangleExcess) hα.1 hα.2.1
    (rhombusArea_strictConcave_equilateral_interval c D.alpha hcI hαI)
    hends.1 hends.2 (faceCornerCount D.tri v) θ hθclosed hsumθ
  have hcard : Fintype.card ↥(faceCornersAt D.quad v) = faceCornerCount D.quad v :=
    (faceCornerCount_eq_fintype_card D.quad v).symm
  rw [hcard, hsumA] at hbound
  change 0 < _ ∧ _
  refine ⟨hpos, ?_, ?_⟩
  · dsimp [localArea, beta]
    nlinarith
  · intro heq
    have heqA : (∑ p, rhombusArea (1 / c) (θ p)) =
        (Fintype.card ↥(faceCornersAt D.quad v) : ℝ) * (2 * D.triangleExcess) +
        (rhombusArea (1 / c) D.beta - 2 * D.triangleExcess) := by
      rw [hcard, hsumA]
      dsimp [localArea] at heq
      nlinarith
    obtain ⟨hcount, htri, hall⟩ := hequality hθ heqA
    refine ⟨by simpa [hcard] using hcount, htri, ?_⟩
    intro p hp
    exact hall ⟨p, hp⟩

theorem packing_and_euler (D : ContactTilingData Y c) (hY : IsConfiguration Y)
    (hc : 0 < c) (hcupper : c ≤ aInf) : c = aInf ∧ D.triCount + 2 * D.quadCount = 12 := by
  have hlocal : ∀ v : Fin 8,
      ((faceCornerCount D.tri v : ℝ) + 2 * (faceCornerCount D.quad v : ℝ)) * (3 * D.alpha - Real.pi) +
        (2 * D.beta + 2 * D.gamma - 6 * D.alpha) ≤ D.localArea v := by
    intro v
    have h := (D.local_area_reduction hY hc hcupper v).2.1
    dsimp [triangleExcess, rhombusArea, gamma] at h ⊢
    linarith
  have htri : ∑ v, (faceCornerCount D.tri v : ℝ) = 3 * (D.triCount : ℝ) := by
    simpa using sum_faceCornerCount D.tri
  have hquad : ∑ v, (faceCornerCount D.quad v : ℝ) = 4 * (D.quadCount : ℝ) := by
    simpa using sum_faceCornerCount D.quad
  have hstrong := area_inequality_before_euler D.alpha D.beta D.gamma D.triangleTotal
    D.quadTotal D.triCount D.quadCount (faceCornerCount D.tri) (faceCornerCount D.quad)
    D.localArea hlocal D.sum_localArea htri hquad rfl D.total_excess_before_euler
  apply packing_euler_count_eq c (D.triCount + 2 * D.quadCount) hc hcupper D.euler_lower_bound
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, alpha, beta, gamma] using hstrong

/-- Exact Euler equality is a consequence, not an input, in the packing range. -/
theorem euler (D : ContactTilingData Y c) (hY : IsConfiguration Y)
    (hc : 0 < c) (hcupper : c ≤ aInf) : D.triCount + 2 * D.quadCount = 12 :=
  (D.packing_and_euler hY hc hcupper).2

theorem total_excess (D : ContactTilingData Y c) (hY : IsConfiguration Y)
    (hc : 0 < c) (hcupper : c ≤ aInf) : D.triangleTotal + D.quadTotal = 4 * Real.pi := by
  have heuler : (D.triCount : ℝ) + 2 * (D.quadCount : ℝ) = 12 := by
    exact_mod_cast D.euler hY hc hcupper
  rw [D.total_excess_before_euler, heuler]
  ring

theorem area_bound (D : ContactTilingData Y c) (hY : IsConfiguration Y)
    (hc : 0 < c) (hcupper : c ≤ aInf) :
    6 * D.alpha + D.beta + D.gamma ≤ 4 * Real.pi ∧
      (6 * D.alpha + D.beta + D.gamma = 4 * Real.pi → ∀ v : Fin 8,
        D.localArea v = ((faceCornerCount D.tri v : ℝ) + 2 * (faceCornerCount D.quad v : ℝ)) * D.triangleExcess +
          (rhombusArea (1 / c) D.beta - 2 * D.triangleExcess)) := by
  have hlocal : ∀ v : Fin 8,
      ((faceCornerCount D.tri v : ℝ) + 2 * (faceCornerCount D.quad v : ℝ)) * (3 * D.alpha - Real.pi) +
        (2 * D.beta + 2 * D.gamma - 6 * D.alpha) ≤ D.localArea v := by
    intro v
    have h := (D.local_area_reduction hY hc hcupper v).2.1
    dsimp [triangleExcess, rhombusArea, gamma] at h ⊢
    linarith
  have htri : ∑ v, (faceCornerCount D.tri v : ℝ) = 3 * (D.triCount : ℝ) := by
    simpa using sum_faceCornerCount D.tri
  have hquad : ∑ v, (faceCornerCount D.quad v : ℝ) = 4 * (D.quadCount : ℝ) := by
    simpa using sum_faceCornerCount D.quad
  obtain ⟨hbound, heq⟩ := area_inequality_from_incidence D.alpha D.beta D.gamma D.triangleTotal
    D.quadTotal D.triCount D.quadCount (faceCornerCount D.tri) (faceCornerCount D.quad)
    D.localArea hlocal D.sum_localArea htri hquad rfl (D.total_excess hY hc hcupper) (D.euler hY hc hcupper)
  refine ⟨hbound, ?_⟩
  intro h v
  have hv := heq h v
  dsimp [triangleExcess, rhombusArea, gamma] at hv ⊢
  linarith

lemma beta_mem_Ioo (D : ContactTilingData Y c) (hc : 0 < c) (hcupper : c ≤ aInf) :
    D.beta ∈ Set.Ioo (0 : ℝ) Real.pi := by
  have hα := packing_equilateral_angle_range c hc hcupper
  dsimp [beta, alpha]
  constructor <;> linarith [hα.1, hα.2.1, Real.pi_pos]

theorem packing_bound (D : ContactTilingData Y c) (hY : IsConfiguration Y)
    (hc : 0 < c) (hcupper : c ≤ aInf) : aInf ≤ c := by
  have hcI : c ∈ Set.Ioo (0 : ℝ) 1 := ⟨hc, hcupper.trans_lt aInf_mem_Ioo.2⟩
  have hα := packing_equilateral_angle_range c hc hcupper
  have hβ := D.beta_mem_Ioo hc hcupper
  have hγ := rhombusDelta_mem_Ioo (1 / c) D.beta (one_div_pos.mpr hc) hβ
  exact packing_bound_from_angles c D.alpha D.beta D.gamma hcI hα.2.2 rfl hβ hγ
    (rhombusDelta_tan_relation (1 / c) D.beta hβ) (D.area_bound hY hc hcupper).1

theorem equality_incidence (D : ContactTilingData Y aInf) (hY : IsConfiguration Y) :
    ∀ v : Fin 8, faceCornerCount D.quad v = 1 ∧ faceCornerCount D.tri v = 3 ∧
      ∀ p ∈ faceCornersAt D.quad v, D.angle p.1 p.2 = D.beta := by
  have hα := packing_equilateral_angle_range aInf aInf_mem_Ioo.1 le_rfl
  have hβ := D.beta_mem_Ioo aInf_mem_Ioo.1 le_rfl
  have hγ := rhombusDelta_mem_Ioo (1 / aInf) D.beta (one_div_pos.mpr aInf_mem_Ioo.1) hβ
  have heq := (packing_angles_equality D.alpha D.beta D.gamma hα.2.2 rfl hβ hγ
    (rhombusDelta_tan_relation (1 / aInf) D.beta hβ)).2
  have hlocal := (D.area_bound hY aInf_mem_Ioo.1 le_rfl).2 heq
  intro v
  exact (D.local_area_reduction hY aInf_mem_Ioo.1 le_rfl v).2.2 (hlocal v)

theorem equality_face_counts (D : ContactTilingData Y aInf) (hY : IsConfiguration Y) :
    D.triCount = 8 ∧ D.quadCount = 2 := by
  have heq := D.equality_incidence hY
  have ht := sum_faceCornerCount D.tri
  have hq := sum_faceCornerCount D.quad
  have htsum : (∑ v, (faceCornerCount D.tri v : ℝ)) = 24 := by
    calc
      _ = ∑ _v : Fin 8, (3 : ℝ) := Finset.sum_congr rfl (fun v _ => by rw [(heq v).2.1]; norm_num)
      _ = 24 := by norm_num
  have hqsum : (∑ v, (faceCornerCount D.quad v : ℝ)) = 8 := by
    calc
      _ = ∑ _v : Fin 8, (1 : ℝ) := Finset.sum_congr rfl (fun v _ => by rw [(heq v).1]; norm_num)
      _ = 8 := by norm_num
  rw [htsum] at ht
  rw [hqsum] at hq
  norm_num only [Nat.cast_ofNat] at ht hq
  constructor
  · have h : (D.triCount : ℝ) = 8 := by linarith
    exact_mod_cast h
  · have h : (D.quadCount : ℝ) = 2 := by linarith
    exact_mod_cast h

lemma corner_mem (D : ContactTilingData Y c) (f : Fin D.quadCount) (j : Fin 4) :
    (f, j) ∈ faceCornersAt D.quad (D.quad f j) := by simp [faceCornersAt]

theorem equality_quad_angles (D : ContactTilingData Y aInf) (hY : IsConfiguration Y)
    (f : Fin D.quadCount) (j : Fin 4) : D.angle f j = D.beta := by
  have h := D.equality_incidence hY (D.quad f j)
  exact h.2.2 (f, j) (D.corner_mem f j)

theorem equality_quads_disjoint (D : ContactTilingData Y aInf) (hY : IsConfiguration Y)
    (f g : Fin D.quadCount) (i j : Fin 4) (heq : D.quad f i = D.quad g j) : f = g := by
  have hcard : (faceCornersAt D.quad (D.quad f i)).card = 1 :=
    (D.equality_incidence hY (D.quad f i)).1
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcard
  have hf := D.corner_mem f i
  have hg : (g, j) ∈ faceCornersAt D.quad (D.quad f i) := by
    rw [heq]
    exact D.corner_mem g j
  rw [hp, Finset.mem_singleton] at hf hg
  exact congrArg Prod.fst (hf.trans hg.symm)

/-- The only boundary-adjacency consequence needed for rigidity. A
quadrilateral boundary edge either has an exterior contact triangle or
meets a second quadrilateral face. This is not an existence assertion. -/
def BoundaryAdjacency (D : ContactTilingData Y c) : Prop :=
  ∀ f : Fin D.quadCount, ∀ j : Fin 4,
    (∃ k : Fin 8, (∀ i : Fin 4, k ≠ D.quad f i) ∧
      inner ℝ (Y (D.quad f j)) (Y k) = c ∧
        inner ℝ (Y (D.quad f (j + 1))) (Y k) = c) ∨
    (∃ g : Fin D.quadCount, g ≠ f ∧ ∃ i : Fin 4, D.quad g i = D.quad f j)

end ContactTilingData
end SquareAntiprismVerification
