import ThomsonNegative.Structure.Concrete.MapBridge
import ThomsonNegative.Certificate.Correction.SourceSound
import ThomsonNegative.Certificate.Bridges.InverseUniqueness

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Structure.Concrete
open ThomsonNegative.Structure.Exact ThomsonNegative.Structure.Packed

def sourceMatrix (u : ℝ) : Matrix (Fin 68) (Fin 68) ℝ := fun r c =>
  evalZ (recCoeffs (ThomsonNegative.Certificate.Correction.Source.rowNumerator r.val c.val)) u /
    evalZ (recCoeffs (ThomsonNegative.Certificate.Correction.Source.rowDenominator r.val)) u

def sourceRepair (u : ℝ) : ChartSpace →ₗ[ℝ] ChartSpace where
  toFun x r := ThomsonNegative.Certificate.Correction.Source.rowLinear u r.val x
  map_add' x y := by funext r;exact map_add _ x y
  map_smul' c x := by funext r;exact map_smul _ c x

theorem sourceRepair_matrix (u : ℝ) (x : ChartSpace) :
    sourceRepair u x=(sourceMatrix u).mulVec x := by
  funext r
  exact ThomsonNegative.Certificate.Correction.Source.rowLinear_apply u r x

/-- The unique shared source-table correction used by the finite arithmetic. -/
def sourceCorrection (u : ℝ) : ChartSpace →ₗ[ℝ] GramFamily where
  toFun x b i j := ThomsonNegative.Certificate.Correction.Source.rowLinear u
    (ThomsonNegative.Certificate.Correction.Source.blockIndex b.val i.val j.val) x
  map_add' x y := by funext b i j;exact map_add _ x y
  map_smul' c x := by funext b i j;exact map_smul _ c x

@[simp] theorem sourceCorrection_entry (u : ℝ) (x : ChartSpace)
    (b : Block) (i j : Fin (blockSize b)) :
    sourceCorrection u x b i j=ThomsonNegative.Certificate.Correction.Source.rowLinear u
      (ThomsonNegative.Certificate.Correction.Source.blockIndex b.val i.val j.val) x := rfl

theorem insert_sourceRepair (u : ℝ) (x : ChartSpace) :
    insertRepair (sourceRepair u x)=sourceCorrection u x := by
  funext b i j
  rw [insertRepair_entry]
  by_cases h : ThomsonNegative.Certificate.Correction.Source.blockIndex b.val i.val j.val<68
  · simp only [h,dif_pos,sourceRepair,sourceCorrection_entry,LinearMap.coe_mk,AddHom.coe_mk]
  · simp [h,sourceCorrection_entry,ThomsonNegative.Certificate.Correction.Source.rowLinear]

theorem sourceCorrection_eq_staged_of_identity (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3)
    (hD : Factored.HighData.A.eval a*sourceMatrix (a-83/256)=1) :
    sourceCorrection (a-83/256)=(stagedRightInverse a ha hb).correction := by
  have hR : (Matrix.toLin' (Factored.HighData.A.eval a)).comp (Factored.operatorRepair a)=LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact Factored.operatorRepair_right_inverse a ha hb x
  have hS : (Matrix.toLin' (Factored.HighData.A.eval a)).comp (sourceRepair (a-83/256))=LinearMap.id := by
    apply LinearMap.ext
    intro x
    change (Factored.HighData.A.eval a).mulVec (sourceRepair (a-83/256) x)=x
    rw [sourceRepair_matrix,Matrix.mulVec_mulVec,hD,Matrix.one_mulVec]
  have he := ThomsonNegative.Certificate.Bridges.finite_rightInverse_unique
    (Matrix.toLin' (Factored.HighData.A.eval a)) (Factored.operatorRepair a)
    (sourceRepair (a-83/256)) hR hS
  apply LinearMap.ext
  intro x
  rw [← insert_sourceRepair,← he]
  rfl

def rightInverseOfSourceIdentity (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3)
    (hD : Factored.HighData.A.eval a*sourceMatrix (a-83/256)=1) :
    HybridRightInverse (system a ha hb) where
  correction := sourceCorrection (a-83/256)
  right_inverse := by
    rw [sourceCorrection_eq_staged_of_identity a ha hb hD]
    exact (stagedRightInverse a ha hb).right_inverse

#print axioms sourceCorrection_eq_staged_of_identity
end ThomsonNegative.Structure.Concrete
