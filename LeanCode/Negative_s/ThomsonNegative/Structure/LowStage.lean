import Mathlib

/-! A factored low-degree solve. No expanded right-inverse table appears in the theorem. -/

noncomputable section

namespace ThomsonNegative.Structure

section LowStage

variable {V U W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup U] [Module ℝ U] [AddCommGroup W] [Module ℝ W]

structure LowStageData (V U W : Type*) [AddCommGroup V] [Module ℝ V]
    [AddCommGroup U] [Module ℝ U] [AddCommGroup W] [Module ℝ W] where
  momentColumns : U →ₗ[ℝ] V
  scalarColumns : W →ₗ[ℝ] V
  jets : V →ₗ[ℝ] U
  scalarRows : V →ₗ[ℝ] W
  momentInverse : U →ₗ[ℝ] U
  scalarInverse : W →ₗ[ℝ] W
  moment_identity : (jets.comp momentColumns).comp momentInverse = LinearMap.id
  scalar_identity : (scalarRows.comp scalarColumns).comp scalarInverse = LinearMap.id
  scalar_jet_zero : jets.comp scalarColumns = 0
  coordinates_injective : ∀ v, jets v = 0 → scalarRows v = 0 → v = 0

def LowStageData.momentSolve (D : LowStageData V U W) : V →ₗ[ℝ] U :=
  D.momentInverse.comp D.jets

def LowStageData.scalarSolve (D : LowStageData V U W) : V →ₗ[ℝ] W :=
  D.scalarInverse.comp (D.scalarRows.comp
    (LinearMap.id - D.momentColumns.comp D.momentSolve))

theorem LowStageData.recovery (D : LowStageData V U W) (v : V) :
    D.momentColumns (D.momentSolve v) + D.scalarColumns (D.scalarSolve v) = v := by
  have hm (u : U) : D.jets (D.momentColumns (D.momentInverse u)) = u := by
    exact LinearMap.congr_fun D.moment_identity u
  have hs (w : W) : D.scalarRows (D.scalarColumns (D.scalarInverse w)) = w := by
    exact LinearMap.congr_fun D.scalar_identity w
  have hj (w : W) : D.jets (D.scalarColumns w) = 0 := by
    exact LinearMap.congr_fun D.scalar_jet_zero w
  let z := v - D.momentColumns (D.momentSolve v)
  have hz : D.jets z = 0 := by
    simp [z, LowStageData.momentSolve, hm]
  have hw : D.scalarSolve v = D.scalarInverse (D.scalarRows z) := rfl
  have hzero : z - D.scalarColumns (D.scalarSolve v) = 0 := by
    apply D.coordinates_injective
    · simp [map_sub, hz, hj]
    · simp [map_sub, hw, hs]
  have he := sub_eq_zero.mp hzero
  rw [← he]
  dsimp [z]
  abel

theorem LowStageData.gram_recovery (D : LowStageData V U W)
    {G : Type*} [AddCommGroup G] [Module ℝ G]
    (coefficientMap : G →ₗ[ℝ] V) (insertMoment : U →ₗ[ℝ] G)
    (insertScalar : W →ₗ[ℝ] G)
    (hm : coefficientMap.comp insertMoment = D.momentColumns)
    (hs : coefficientMap.comp insertScalar = D.scalarColumns) (v : V) :
    coefficientMap (insertMoment (D.momentSolve v) + insertScalar (D.scalarSolve v)) = v := by
  rw [map_add]
  change (coefficientMap.comp insertMoment) _ + (coefficientMap.comp insertScalar) _ = v
  rw [hm, hs]
  exact D.recovery v

end LowStage

end ThomsonNegative.Structure
