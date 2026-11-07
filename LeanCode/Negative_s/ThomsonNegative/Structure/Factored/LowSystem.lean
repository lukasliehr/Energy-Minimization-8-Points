import ThomsonNegative.Structure.Factored.MatrixIdentities
import ThomsonNegative.Structure.LowStage

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Structure.Factored
open ThomsonNegative.Structure.Exact

def pivotIndex : Fin 36 → Fin 51 := ![50,49,48,47,46,45,44,43,42,41,40,39,38,37,36,35,34,33,32,31,30,29,28,27,26,25,24,23,22,21,20,19,18,17,16,15]
def complementIndex : Fin 15 → Fin 51 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14]

def lowSplit : Sum (Fin 15) (Fin 36) → Fin 51 := Sum.elim complementIndex pivotIndex

theorem lowSplit_bijective : Function.Bijective lowSplit := by decide +kernel

def lowSplitEquiv : Sum (Fin 15) (Fin 36) ≃ Fin 51 :=
  Equiv.ofBijective lowSplit lowSplit_bijective

theorem pivotIndex_agree : ∀ i : Fin 36, Data.pivotRows i.val=(pivotIndex i).val := by decide +kernel
theorem complementIndex_agree : ∀ i : Fin 15,
    Data.complementColumns i.val=(complementIndex i).val := by decide +kernel

def scalarRows : (Fin 51 → ℝ) →ₗ[ℝ] (Fin 36 → ℝ) where
  toFun := fun v i => v (pivotIndex i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def complementRows (v : Fin 51 → ℝ) : Fin 15 → ℝ := fun i => v (complementIndex i)

theorem lowSplit_sum (f : Fin 51 → ℝ) :
    (∑ k, f k) = (∑ i : Fin 15, f (complementIndex i)) +
      ∑ j : Fin 36, f (pivotIndex j) := by
  rw [← Equiv.sum_comp lowSplitEquiv f, Fintype.sum_sum_type]
  rfl

theorem JC_eval (a : ℝ) : Data.JC.eval a=(Data.J.eval a).submatrix id complementIndex := by
  ext i j
  simp only [Data.JC, EncodedMatrix.eval, EncodedMatrix.cols, Matrix.submatrix_apply,
    id_eq, complementIndex_agree]

theorem SM_eval (a : ℝ) : Data.SM.eval a=(Data.S.eval a).submatrix pivotIndex id := by
  ext i j
  simp only [Data.SM, EncodedMatrix.eval, EncodedMatrix.rows, Matrix.submatrix_apply,
    id_eq, pivotIndex_agree]

theorem scalarRows_matrix (a : ℝ) :
    scalarRows.comp (Matrix.toLin' (Data.S.eval a))=Matrix.toLin' (Data.SM.eval a) := by
  rw [SM_eval]
  ext v i
  rfl

theorem low_coordinates_injective (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3)
    (v : Fin 51 → ℝ) (hj : (Data.J.eval a).mulVec v=0) (he : scalarRows v=0) : v=0 := by
  have hc : (Data.JC.eval a).mulVec (complementRows v)=0 := by
    rw [JC_eval]
    funext i
    have hh := congrFun hj i
    change (∑ k : Fin 51, (Data.J.eval a) i k * v k)=0 at hh
    rw [lowSplit_sum] at hh
    have hzero : (∑ j : Fin 36, (Data.J.eval a) i (pivotIndex j) * v (pivotIndex j))=0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hv := congrFun he j
      change v (pivotIndex j)=0 at hv
      rw [hv,mul_zero]
    rw [hzero,add_zero] at hh
    simpa only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id_eq, complementRows, Pi.zero_apply] using hh
  have hleft := congrArg (fun w => (Data.CI.eval a).mulVec w) hc
  rw [Matrix.mulVec_mulVec, complement_inverse_identity a ha hb] at hleft
  have hvcomp : complementRows v=0 := by simpa using hleft
  funext k
  obtain ⟨z,hz⟩ := lowSplit_bijective.2 k
  rcases z with i | j
  · subst k
    exact congrFun hvcomp i
  · subst k
    exact congrFun he j

def lowStage (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) :
    ThomsonNegative.Structure.LowStageData (Fin 51 → ℝ) (Fin 15 → ℝ) (Fin 36 → ℝ) where
  momentColumns := Matrix.toLin' (Data.P.eval a)
  scalarColumns := Matrix.toLin' (Data.S.eval a)
  jets := Matrix.toLin' (Data.J.eval a)
  scalarRows := scalarRows
  momentInverse := Matrix.toLin' (Data.MI.eval a)
  scalarInverse := Matrix.toLin' (Data.SI.eval a)
  moment_identity := by
    have h : Matrix.toLin' ((Data.J.eval a * Data.P.eval a) * Data.MI.eval a)=LinearMap.id := by
      rw [moment_jets_identity a ha hb, moment_inverse_identity a ha hb, Matrix.toLin'_one]
    simpa only [Matrix.toLin'_mul] using h
  scalar_identity := by
    rw [scalarRows_matrix, ← Matrix.toLin'_mul, scalar_inverse_identity a ha hb, Matrix.toLin'_one]
  scalar_jet_zero := by
    have h := congrArg Matrix.toLin' (scalar_zero_jets_identity a ha hb)
    simpa only [Matrix.toLin'_mul, map_zero] using h
  coordinates_injective := fun v hj he => low_coordinates_injective a ha hb v hj he

theorem lowStage_recovery (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) (v : Fin 51 → ℝ) :
    (lowStage a ha hb).momentColumns ((lowStage a ha hb).momentSolve v) +
      (lowStage a ha hb).scalarColumns ((lowStage a ha hb).scalarSolve v) = v :=
  (lowStage a ha hb).recovery v

#print axioms lowStage_recovery
end ThomsonNegative.Structure.Factored
