import ThomsonNegative.Geometry.Base

noncomputable section
open Real
open scoped BigOperators
namespace ThomsonNegative.Geometry
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
lemma inner_coordinate_sum (x y : Point) : inner ℝ x y=∑ i,x i*y i := by
  simp [PiLp.inner_apply,RCLike.inner_apply,mul_comm]
def crossVec (x y : ℝ³) : ℝ³ :=
  !₂[x 1 * y 2 - x 2 * y 1, x 2 * y 0 - x 0 * y 2, x 0 * y 1 - x 1 * y 0]

lemma crossVec_inner_left (x y : ℝ³) : inner ℝ (crossVec x y) x = 0 := by
  simp [crossVec, inner_coordinate_sum, Fin.sum_univ_succ]
  ring

lemma crossVec_inner_right (x y : ℝ³) : inner ℝ (crossVec x y) y = 0 := by
  simp [crossVec, inner_coordinate_sum, Fin.sum_univ_succ]
  ring

lemma crossVec_norm_sq (x y : ℝ³) :
    ‖crossVec x y‖ ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 - inner ℝ x y ^ 2 := by
  simp only [← real_inner_self_eq_norm_sq, inner_coordinate_sum]
  simp [crossVec, Fin.sum_univ_succ]
  ring


namespace SquareTools
abbrev r (a : ℝ) : ℝ := √(1-a)
abbrev h (a : ℝ) : ℝ := √a
def rhombusGram (c x y : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![1,c,x,c],![c,1,c,y],![x,c,1,c],![c,y,c,1]]
def frameLinearMap (e : Fin 3 → ℝ³) : ℝ³ →ₗ[ℝ] ℝ³ where
  toFun x := ∑ i, x i • e i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.smul_sum, smul_smul]

lemma frameLinearMap_inner (e : Fin 3 → ℝ³)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) (x y : ℝ³) :
    inner ℝ (frameLinearMap e x) (frameLinearMap e y) = inner ℝ x y := by
  change inner ℝ (∑ i, x i • e i) (∑ j, y j • e j) = _
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_trivial, he]
  simp [inner_coordinate_sum, mul_comm]

def frameLinearIsometry (e : Fin 3 → ℝ³)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) : ℝ³ →ₗᵢ[ℝ] ℝ³ where
  toLinearMap := frameLinearMap e
  norm_map' x := by
    have h := frameLinearMap_inner e he x x
    simp only [real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg (frameLinearMap e x), norm_nonneg x]

def frameEquiv (e : Fin 3 → ℝ³)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) : ℝ³ ≃ₗᵢ[ℝ] ℝ³ :=
  LinearIsometryEquiv.ofSurjective (frameLinearIsometry e he)
    (LinearMap.surjective_of_injective (f := (frameLinearIsometry e he).toLinearMap)
      (frameLinearIsometry e he).injective)

lemma frameEquiv_apply (e : Fin 3 → ℝ³)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) (x : ℝ³) :
    frameEquiv e he x = ∑ i, x i • e i := rfl

lemma square_gram_of_diagonals (Y : Fin 4 → ℝ³) (c : ℝ)
    (hY : ∀ i, ‖Y i‖ = 1)
    (h01 : inner ℝ (Y 0) (Y 1) = c) (h12 : inner ℝ (Y 1) (Y 2) = c)
    (h23 : inner ℝ (Y 2) (Y 3) = c) (h30 : inner ℝ (Y 3) (Y 0) = c)
    (h02 : inner ℝ (Y 0) (Y 2) = 2 * c - 1) (h13 : inner ℝ (Y 1) (Y 3) = 2 * c - 1) :
    ∀ i j, inner ℝ (Y i) (Y j) = rhombusGram c (2 * c - 1) (2 * c - 1) i j := by
  have h10 := (real_inner_comm (Y 0) (Y 1)).trans h01
  have h21 := (real_inner_comm (Y 1) (Y 2)).trans h12
  have h32 := (real_inner_comm (Y 2) (Y 3)).trans h23
  have h03 := (real_inner_comm (Y 3) (Y 0)).trans h30
  have h20 := (real_inner_comm (Y 0) (Y 2)).trans h02
  have h31 := (real_inner_comm (Y 1) (Y 3)).trans h13
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [rhombusGram, hY, h01, h12, h23, h30, h02, h13, h10, h21, h32, h03, h20, h31]

def squareRawFrame (Y : Fin 4 → ℝ³) : Fin 3 → ℝ³ :=
  ![Y 0 - Y 2, Y 1 - Y 3, Y 0 + Y 2]

lemma rhombusGram_regular_entry (c : ℝ) (i j : Fin 4) :
    rhombusGram c (2 * c - 1) (2 * c - 1) i j =
      if i = j then 1 else if i.val + j.val = 2 ∨ i.val + j.val = 4 then 2 * c - 1 else c := by
  fin_cases i <;> fin_cases j <;> rfl

lemma square_raw_frame_gram (Y : Fin 4 → ℝ³) (c : ℝ)
    (hgram : ∀ i j, inner ℝ (Y i) (Y j) = rhombusGram c (2 * c - 1) (2 * c - 1) i j) :
    ∀ i j, inner ℝ (squareRawFrame Y i) (squareRawFrame Y j) =
      if i = j then (if i = 2 then 4 * c else 4 * (1 - c)) else 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    dsimp [squareRawFrame] <;>
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, hgram,
      rhombusGram_regular_entry] <;> norm_num [Fin.ext_iff] <;> ring

lemma square_alternating_relation (Y : Fin 4 → ℝ³) (c : ℝ)
    (hgram : ∀ i j, inner ℝ (Y i) (Y j) = rhombusGram c (2 * c - 1) (2 * c - 1) i j) :
    Y 0 - Y 1 + Y 2 - Y 3 = 0 := by
  have hnorm : ‖Y 0 - Y 1 + Y 2 - Y 3‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, hgram,
      rhombusGram_regular_entry]
    norm_num [Fin.ext_iff]
    ring
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (Y 0 - Y 1 + Y 2 - Y 3)])

def squareFrame (Y : Fin 4 → ℝ³) (c : ℝ) : Fin 3 → ℝ³ :=
  fun i => (2 * Real.sqrt (if i = 2 then c else 1 - c))⁻¹ • squareRawFrame Y i

theorem square_frame_orthonormal (Y : Fin 4 → ℝ³) (c : ℝ)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hgram : ∀ i j, inner ℝ (Y i) (Y j) = rhombusGram c (2 * c - 1) (2 * c - 1) i j) :
    ∀ i j, inner ℝ (squareFrame Y c i) (squareFrame Y c j) = if i = j then 1 else 0 := by
  intro i j
  have hraw := square_raw_frame_gram Y c hgram i j
  simp only [squareFrame, inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial, hraw]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    split_ifs with hi
    · have hs := Real.sq_sqrt hc.1.le
      have hn := (Real.sqrt_pos.mpr hc.1).ne'
      field_simp
      nlinarith
    · have hs := Real.sq_sqrt (by linarith [hc.2] : 0 ≤ 1 - c)
      have hn := (Real.sqrt_pos.mpr (by linarith [hc.2] : 0 < 1 - c)).ne'
      field_simp
      nlinarith
  · simp [hij]

theorem square_frame_representation (Y : Fin 4 → ℝ³) (c : ℝ)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hgram : ∀ i j, inner ℝ (Y i) (Y j) = rhombusGram c (2 * c - 1) (2 * c - 1) i j) :
    ∀ j : Fin 4, frameEquiv (squareFrame Y c) (square_frame_orthonormal Y c hc hgram)
      (X c (Fin.castAdd 4 j)) = Y j := by
  have hrpos : 0 < r c := Real.sqrt_pos.mpr (by linarith [hc.2])
  have hhpos : 0 < h c := Real.sqrt_pos.mpr hc.1
  have hrc : r c * (2 * r c)⁻¹ = (1 / 2 : ℝ) := by field_simp
  have hhc : h c * (2 * h c)⁻¹ = (1 / 2 : ℝ) := by field_simp
  have he0 : squareFrame Y c 0 = (2 * r c)⁻¹ • (Y 0 - Y 2) := rfl
  have he1 : squareFrame Y c 1 = (2 * r c)⁻¹ • (Y 1 - Y 3) := rfl
  have he2 : squareFrame Y c 2 = (2 * h c)⁻¹ • (Y 0 + Y 2) := rfl
  have halt := square_alternating_relation Y c hgram
  intro j
  rw [frameEquiv_apply]
  fin_cases j
  · change r c • squareFrame Y c 0 + (0 • squareFrame Y c 1 + (h c • squareFrame Y c 2 + 0)) = Y 0
    simp only [zero_smul, zero_add, add_zero, he0, he2, smul_smul, hrc, hhc]
    module
  · change 0 • squareFrame Y c 0 + (r c • squareFrame Y c 1 + (h c • squareFrame Y c 2 + 0)) = Y 1
    simp only [zero_smul, zero_add, add_zero, he1, he2, smul_smul, hrc, hhc]
    calc
      _ = Y 1 + (1 / 2 : ℝ) • (Y 0 - Y 1 + Y 2 - Y 3) := by module
      _ = Y 1 := by rw [halt]; simp
  · change (-r c) • squareFrame Y c 0 + (0 • squareFrame Y c 1 + (h c • squareFrame Y c 2 + 0)) = Y 2
    simp only [zero_smul, zero_add, add_zero, he0, he2, smul_smul, neg_mul, hrc, hhc]
    module
  · change 0 • squareFrame Y c 0 + ((-r c) • squareFrame Y c 1 + (h c • squareFrame Y c 2 + 0)) = Y 3
    simp only [zero_smul, zero_add, add_zero, he1, he2, smul_smul, neg_mul, hrc, hhc]
    calc
      _ = Y 3 + (1 / 2 : ℝ) • (Y 0 - Y 1 + Y 2 - Y 3) := by module
      _ = Y 3 := by rw [halt]; simp

theorem square_gram_congruent (Y : Fin 4 → ℝ³) (c : ℝ)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hgram : ∀ i j, inner ℝ (Y i) (Y j) = rhombusGram c (2 * c - 1) (2 * c - 1) i j) :
    ∃ U : ℝ³ ≃ₗᵢ[ℝ] ℝ³, ∀ j : Fin 4, U (X c (Fin.castAdd 4 j)) = Y j :=
  ⟨frameEquiv (squareFrame Y c) (square_frame_orthonormal Y c hc hgram),
    square_frame_representation Y c hc hgram⟩


#print axioms square_gram_congruent
end SquareTools
end ThomsonNegative.Geometry
