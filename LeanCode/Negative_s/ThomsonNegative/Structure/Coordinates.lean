import ThomsonNegative.Structure.Basic
import ThomsonNegative.Structure.Compatibility

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Structure

abbrev FullSpace := Fin 102 → ℝ
abbrev ChartSpace := Fin 68 → ℝ

def fullTag : Fin 102 → Tag := ![(0,0,0), (1,0,0), (0,1,0), (2,0,0), (0,0,1), (1,1,0), (3,0,0), (0,2,0), (1,0,1), (2,1,0), (4,0,0), (0,1,1), (1,2,0), (2,0,1), (3,1,0), (5,0,0), (0,0,2), (0,3,0), (1,1,1), (2,2,0), (3,0,1), (4,1,0), (6,0,0), (0,2,1), (1,0,2), (1,3,0), (2,1,1), (3,2,0), (4,0,1), (5,1,0), (7,0,0), (0,1,2), (0,4,0), (1,2,1), (2,0,2), (2,3,0), (3,1,1), (4,2,0), (5,0,1), (6,1,0), (8,0,0), (0,0,3), (0,3,1), (1,1,2), (1,4,0), (2,2,1), (3,0,2), (3,3,0), (4,1,1), (5,2,0), (6,0,1), (7,1,0), (9,0,0), (0,2,2), (0,5,0), (1,0,3), (1,3,1), (2,1,2), (2,4,0), (3,2,1), (4,0,2), (4,3,0), (5,1,1), (6,2,0), (7,0,1), (8,1,0), (10,0,0), (0,1,3), (0,4,1), (1,2,2), (1,5,0), (2,0,3), (2,3,1), (3,1,2), (3,4,0), (4,2,1), (5,0,2), (5,3,0), (6,1,1), (7,2,0), (8,0,1), (9,1,0), (11,0,0), (0,0,4), (0,3,2), (0,6,0), (1,1,3), (1,4,1), (2,2,2), (2,5,0), (3,0,3), (3,3,1), (4,1,2), (4,4,0), (5,2,1), (6,0,2), (6,3,0), (7,1,1), (8,2,0), (9,0,1), (10,1,0), (12,0,0)]

def chartIndex : Fin 68 → Fin 102 := ![1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 82, 101, 68]

def chartTag (i : Fin 68) : Tag := fullTag (chartIndex i)

def highPivot : Fin 3 → Fin 35 := ![15, 34, 1]

def highReconstruction : Matrix (Fin 35) (Fin 3) ℚ := ![![-55, 0, 4],
  ![0, 0, 1],
  ![125, 0, -4],
  ![-8, 0, 0],
  ![-15, 0, 2],
  ![-125, 0, 0],
  ![-95, 0, 0],
  ![55, 0, 0],
  ![165, 0, 0],
  ![33, 0, 0],
  ![-77, 0, 0],
  ![-77, 0, 0],
  ![44, 0, 0],
  ![11, 0, 0],
  ![-11, 0, 0],
  ![1, 0, 0],
  ![0, 21, 0],
  ![0, 12, 0],
  ![0, 8, 0],
  ![0, -120, 0],
  ![0, 24, 0],
  ![0, 234, 0],
  ![0, -36, 0],
  ![0, 28, 0],
  ![0, -240, 0],
  ![0, -180, 0],
  ![0, 105, 0],
  ![0, 252, 0],
  ![0, 42, 0],
  ![0, -112, 0],
  ![0, -96, 0],
  ![0, 54, 0],
  ![0, 12, 0],
  ![0, -12, 0],
  ![0, 1, 0]]

theorem fullTag_injective : Function.Injective fullTag := by decide +kernel

theorem highReconstruction_pivots : ∀ i j : Fin 3,
    highReconstruction (highPivot i) j = if i=j then 1 else 0 := by decide +kernel

def fullCoefficients (p : Poly3) : FullSpace :=
  fun i => MvPolynomial.coeff (tagExponent (fullTag i)) p

def chartCoefficients (p : Poly3) : ChartSpace :=
  fun i => MvPolynomial.coeff (tagExponent (chartTag i)) p

def retain (v : FullSpace) : ChartSpace := fun i => v (chartIndex i)

def retainLinear : FullSpace →ₗ[ℝ] ChartSpace where
  toFun := retain
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def synthesize (v : FullSpace) : Poly3 :=
  ∑ i, MvPolynomial.C (v i) * coordinateMonomial (fullTag i)

def synthesizeLinear : FullSpace →ₗ[ℝ] Poly3 where
  toFun := synthesize
  map_add' v w := by simp [synthesize, add_mul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [synthesize, Pi.smul_apply, smul_eq_mul, map_mul,
      MvPolynomial.smul_eq_C_mul, Finset.mul_sum, RingHom.id_apply, mul_assoc]

def physicalSynthesize : FullSpace →ₗ[ℝ] Poly3 :=
  invariantSubst.toLinearMap.comp synthesizeLinear

def highIndex (i : Fin 35) : Fin 102 := ⟨67+i.val, by omega⟩

def highRebuild (x : Fin 3 → ℝ) (i : Fin 35) : ℝ :=
  ∑ j, (highReconstruction i j : ℝ) * x j

def highCoordinates (v : FullSpace) (i : Fin 3) : ℝ := v (highIndex (highPivot i))

def HighCompatible (v : FullSpace) : Prop :=
  ∀ i : Fin 35, v (highIndex i) = highRebuild (highCoordinates v) i

theorem highRebuild_zero : highRebuild 0 = 0 := by
  funext i
  simp [highRebuild]

theorem highRebuild_add (x y : Fin 3 → ℝ) : highRebuild (x+y) = highRebuild x + highRebuild y := by
  funext i
  simp [highRebuild, mul_add, Finset.sum_add_distrib]

theorem highRebuild_sub (x y : Fin 3 → ℝ) : highRebuild (x-y) = highRebuild x - highRebuild y := by
  funext i
  simp [highRebuild, mul_sub, Finset.sum_sub_distrib]

theorem highCompatible_sub {v w : FullSpace} (hv : HighCompatible v) (hw : HighCompatible w) :
    HighCompatible (v-w) := by
  intro i
  change v (highIndex i)-w (highIndex i) = _
  rw [hv i, hw i]
  have h : highCoordinates (v-w)=highCoordinates v-highCoordinates w := rfl
  rw [h, highRebuild_sub]
  rfl

theorem highCoordinates_rebuild (x : Fin 3 → ℝ) :
    (fun i => highRebuild x (highPivot i)) = x := by
  funext i
  have hh (j : Fin 3) : (highReconstruction (highPivot i) j : ℝ) = if i=j then 1 else 0 := by
    have h := congrArg (Rat.castHom ℝ) (highReconstruction_pivots i j)
    by_cases hij : i=j <;> simpa [hij] using h
  simp [highRebuild, hh]

def chartHighIndex (i : Fin 3) : Fin 68 := ⟨65+i.val, by omega⟩

theorem chartHighIndex_eq : ∀ i : Fin 3,
    chartIndex (chartHighIndex i) = highIndex (highPivot i) := by decide +kernel

theorem chartIndex_ne_zero : ∀ i : Fin 68, chartIndex i ≠ 0 := by decide +kernel
theorem chartIndex_ne_square : ∀ i : Fin 68, chartIndex i ≠ 3 := by decide +kernel

theorem index_classification : ∀ i : Fin 102,
    i=0 ∨ i=3 ∨ (∃ j : Fin 68, chartIndex j=i) ∨
      (∃ j : Fin 35, highIndex j=i) := by decide +kernel

theorem highCoordinates_eq_of_retain_eq {v w : FullSpace} (h : retain v=retain w) :
    highCoordinates v=highCoordinates w := by
  funext i
  have he := congrFun h (chartHighIndex i)
  simpa only [retain, chartHighIndex_eq, highCoordinates] using he

theorem two_missing_of_retain_eq {v w : FullSpace}
    (hv : HighCompatible v) (hw : HighCompatible w) (h : retain v=retain w) :
    v-w = (v 3-w 3) • Pi.single (3 : Fin 102) (1 : ℝ) +
      (v 0-w 0) • Pi.single (0 : Fin 102) (1 : ℝ) := by
  classical
  have hh := highCoordinates_eq_of_retain_eq h
  funext i
  rcases index_classification i with rfl | rfl | ⟨j,rfl⟩ | ⟨j,rfl⟩
  · simp
  · simp
  · have he := congrFun h j
    change v (chartIndex j)=w (chartIndex j) at he
    simp [Pi.single_apply, chartIndex_ne_zero, chartIndex_ne_square, he]
  · have hn0 : highIndex j ≠ 0 := by
      intro he
      have hv := congrArg Fin.val he
      change 67+j.val=0 at hv
      omega
    have hn3 : highIndex j ≠ 3 := by
      intro he
      have hv := congrArg Fin.val he
      change 67+j.val=3 at hv
      omega
    have he : v (highIndex j)=w (highIndex j) := by rw [hv j, hw j, hh]
    simp [Pi.single_apply, hn0, hn3, he]

/-- The 68 retained rows determine every compatible hybrid polynomial. -/
theorem coefficient_recovery (D : CompatibilityData FullSpace)
    (hone : D.one = Pi.single (0 : Fin 102) (1 : ℝ))
    (hsquare : D.square = Pi.single (3 : Fin 102) (1 : ℝ))
    {v w : FullSpace} (hv : HighCompatible v) (hw : HighCompatible w)
    (hv0 : D.ell0 v=0) (hv1 : D.ell1 v=0)
    (hw0 : D.ell0 w=0) (hw1 : D.ell1 w=0) (h : retain v=retain w) : v=w := by
  apply D.equal_of_two_missing v w hv0 hv1 hw0 hw1 (v 0-w 0) (v 3-w 3)
  rw [hone, hsquare]
  exact two_missing_of_retain_eq hv hw h

theorem physical_polynomial_recovery (D : CompatibilityData FullSpace)
    (hone : D.one = Pi.single (0 : Fin 102) (1 : ℝ))
    (hsquare : D.square = Pi.single (3 : Fin 102) (1 : ℝ))
    {v w : FullSpace} (hv : HighCompatible v) (hw : HighCompatible w)
    (hv0 : D.ell0 v=0) (hv1 : D.ell1 v=0)
    (hw0 : D.ell0 w=0) (hw1 : D.ell1 w=0) (h : retain v=retain w) :
    physicalSynthesize v=physicalSynthesize w :=
  congrArg physicalSynthesize (coefficient_recovery D hone hsquare hv hw hv0 hv1 hw0 hw1 h)

end ThomsonNegative.Structure
