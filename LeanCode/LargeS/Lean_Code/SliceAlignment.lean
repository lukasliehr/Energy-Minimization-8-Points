import Lean_Code.LocalRotations
import Lean_Code.SliceTarget

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

def sliceDot (Y : Fin 8 → ℝ³) : ℝ := inner ℝ (Y 1) (Y 0)
def firstAlignment (Y : Fin 8 → ℝ³) : ℝ³ ≃ₗᵢ[ℝ] ℝ³ :=
  alignVector (Y 0) (polarP 0)
def firstAligned (Y : Fin 8 → ℝ³) (i : Fin 8) : ℝ³ := firstAlignment Y (Y i)
def sliceSourcePerp (Y : Fin 8 → ℝ³) : ℝ³ :=
  firstAligned Y 1 - sliceDot Y • polarP 0
def sliceTargetPerp (Y : Fin 8 → ℝ³) : ℝ³ :=
  sliceTarget (sliceDot Y) - sliceDot Y • polarP 0
def sliceAlignment (Y : Fin 8 → ℝ³) : ℝ³ ≃ₗᵢ[ℝ] ℝ³ :=
  (firstAlignment Y).trans (alignVector (sliceSourcePerp Y) (sliceTargetPerp Y))
def alignedConfiguration (Y : Fin 8 → ℝ³) (i : Fin 8) : ℝ³ := sliceAlignment Y (Y i)

lemma firstAligned_zero (Y : Fin 8 → ℝ³) (hY : ‖Y 0‖ = 1) :
    firstAligned Y 0 = polarP 0 :=
  alignVector_maps _ _ (hY.trans (polarP_norm 0).symm)

lemma firstAligned_inner (Y : Fin 8 → ℝ³) (hY : ‖Y 0‖ = 1) :
    inner ℝ (firstAligned Y 1) (polarP 0) = sliceDot Y := by
  rw [← firstAligned_zero Y hY]
  exact (firstAlignment Y).inner_map_map _ _

lemma sliceSourcePerp_orthogonal (Y : Fin 8 → ℝ³) (hY : ‖Y 0‖ = 1) :
    inner ℝ (sliceSourcePerp Y) (polarP 0) = 0 := by
  simp [sliceSourcePerp, inner_sub_left, inner_smul_left, firstAligned_inner Y hY,
    polarP_norm]

lemma sliceTargetPerp_orthogonal (Y : Fin 8 → ℝ³) :
    inner ℝ (sliceTargetPerp Y) (polarP 0) = 0 := by
  simp [sliceTargetPerp, inner_sub_left, inner_smul_left, sliceTarget_inner, polarP_norm]

lemma slice_perp_norm_eq (Y : Fin 8 → ℝ³) (hY : ∀ i, ‖Y i‖ = 1)
    (ht : sliceDot Y ^ 2 ≤ sliceTargetDen) : ‖sliceSourcePerp Y‖ = ‖sliceTargetPerp Y‖ := by
  have hsource : ‖firstAligned Y 1‖ = 1 := by
    rw [firstAligned, (firstAlignment Y).norm_map, hY]
  have hs := inverseSphereChart_norm_sq (polarP 0) (firstAligned Y 1) (polarP_norm 0) hsource
  have htar := inverseSphereChart_norm_sq (polarP 0) (sliceTarget (sliceDot Y))
    (polarP_norm 0) (sliceTarget_norm _ ht)
  rw [firstAligned_inner Y (hY 0)] at hs
  rw [sliceTarget_inner] at htar
  change ‖firstAligned Y 1 - inner ℝ (firstAligned Y 1) (polarP 0) • polarP 0‖ ^ 2 = _ at hs
  rw [firstAligned_inner Y (hY 0)] at hs
  change ‖sliceTarget (sliceDot Y) - inner ℝ (sliceTarget (sliceDot Y)) (polarP 0) • polarP 0‖ ^ 2 = _ at htar
  rw [sliceTarget_inner] at htar
  change ‖sliceSourcePerp Y‖ ^ 2 = _ at hs
  change ‖sliceTargetPerp Y‖ ^ 2 = _ at htar
  nlinarith [norm_nonneg (sliceSourcePerp Y), norm_nonneg (sliceTargetPerp Y)]

lemma alignedConfiguration_zero (Y : Fin 8 → ℝ³) (hY : ‖Y 0‖ = 1) :
    alignedConfiguration Y 0 = polarP 0 := by
  change alignVector (sliceSourcePerp Y) (sliceTargetPerp Y) (firstAligned Y 0) = polarP 0
  rw [firstAligned_zero Y hY]
  exact alignVector_preserves_orthogonal _ _ _
    (sliceSourcePerp_orthogonal Y hY) (sliceTargetPerp_orthogonal Y)

lemma alignedConfiguration_one (Y : Fin 8 → ℝ³) (hY : ∀ i, ‖Y i‖ = 1)
    (ht : sliceDot Y ^ 2 ≤ sliceTargetDen) :
    alignedConfiguration Y 1 = sliceTarget (sliceDot Y) := by
  have hpres := alignVector_preserves_orthogonal (sliceSourcePerp Y) (sliceTargetPerp Y)
    (polarP 0) (sliceSourcePerp_orthogonal Y (hY 0)) (sliceTargetPerp_orthogonal Y)
  have hmaps := alignVector_maps (sliceSourcePerp Y) (sliceTargetPerp Y) (slice_perp_norm_eq Y hY ht)
  change alignVector (sliceSourcePerp Y) (sliceTargetPerp Y) (firstAligned Y 1) = _
  rw [show firstAligned Y 1 = sliceSourcePerp Y + sliceDot Y • polarP 0 by
    unfold sliceSourcePerp; abel, map_add, map_smul, hpres, hmaps]
  simp [sliceTargetPerp]

lemma alignedConfiguration_congruent (Y : Fin 8 → ℝ³) :
    Congruent Y (alignedConfiguration Y) := by
  exact ⟨sliceAlignment Y, Equiv.refl _, fun i => rfl⟩

lemma alignedConfiguration_sphere (Y : Fin 8 → ℝ³) (hY : ∀ i, ‖Y i‖ = 1) :
    ∀ i, ‖alignedConfiguration Y i‖ = 1 := by
  intro i
  exact ((sliceAlignment Y).norm_map _).trans (hY i)

lemma alignedConfiguration_gauge (Y : Fin 8 → ℝ³) (hY : ∀ i, ‖Y i‖ = 1)
    (ht : sliceDot Y ^ 2 ≤ sliceTargetDen) :
    InContactGauge (coordinateInverse (alignedConfiguration Y)) :=
  coordinateInverse_in_gauge _ (sliceDot Y) (alignedConfiguration_zero Y (hY 0))
    (alignedConfiguration_one Y hY ht)

lemma sliceDot_P : sliceDot P = aInf := by
  rw [sliceDot, P_eq_polarP]
  simp [polarP, inner_vec3, h, Real.sq_sqrt aInf_mem_Ioo.1.le, ← pow_two]

lemma firstAligned_P (i : Fin 8) : firstAligned P i = P i := by
  unfold firstAligned firstAlignment
  rw [P_eq_polarP]
  exact alignVector_self _ _

lemma sliceTargetPerp_P_ne : sliceTargetPerp P ≠ 0 := by
  have hnorm := inverseSphereChart_norm_sq (polarP 0) (polarP 1) (polarP_norm 0) (polarP_norm 1)
  have hin : inner ℝ (polarP 1) (polarP 0) = aInf := by simpa [sliceDot, P_eq_polarP] using sliceDot_P
  unfold inverseSphereChart at hnorm
  rw [hin] at hnorm
  have hpos : 0 < 1 - aInf ^ 2 := by nlinarith [aInf_mem_Ioo.1, aInf_mem_Ioo.2]
  intro hz
  have hz' : polarP 1 - aInf • polarP 0 = 0 := by
    simpa [sliceTargetPerp, sliceDot_P, sliceTarget_at_center] using hz
  rw [hz', norm_zero, zero_pow (by decide : 2 ≠ 0)] at hnorm
  linarith

lemma sliceSourcePerp_P : sliceSourcePerp P = sliceTargetPerp P := by
  unfold sliceSourcePerp sliceTargetPerp
  rw [firstAligned_P, sliceDot_P, sliceTarget_at_center, P_eq_polarP]

lemma alignedConfiguration_P : alignedConfiguration P = P := by
  funext i
  change alignVector (sliceSourcePerp P) (sliceTargetPerp P) (firstAligned P i) = P i
  rw [sliceSourcePerp_P, alignVector_self, firstAligned_P]

lemma nonzero_add_self (v : ℝ³) (hv : v ≠ 0) : v + v ≠ 0 := by
  intro hzero
  have hn : ‖(2 : ℝ) • v‖ = 0 := by simpa [two_smul] using congrArg norm hzero
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hn
  linarith

lemma sliceDot_continuous : Continuous sliceDot := by unfold sliceDot; fun_prop

lemma firstAligned_continuousAt : ContinuousAt firstAligned P := by
  apply continuousAt_pi.mpr
  intro i
  have hpne : polarP 0 ≠ 0 := by
    intro hz
    have hn := polarP_norm 0
    rw [hz, norm_zero] at hn
    norm_num at hn
  have h := alignVector_continuousAt (polarP 0) (polarP 0) (P i)
    (nonzero_add_self _ hpne) hpne
  have hbase : ContinuousAt (fun Y : Fin 8 → ℝ³ => ((Y 0, polarP 0), Y i)) P := by fun_prop
  have hh : ContinuousAt (fun p : (ℝ³ × ℝ³) × ℝ³ => alignVector p.1.1 p.1.2 p.2)
      ((P 0, polarP 0), P i) := by simpa only [P_eq_polarP] using h
  exact ContinuousAt.comp (f := fun Y : Fin 8 → ℝ³ => ((Y 0, polarP 0), Y i)) hh hbase

lemma sliceSourcePerp_continuousAt : ContinuousAt sliceSourcePerp P := by
  have hfirst : ContinuousAt (fun Y => firstAligned Y 1) P :=
    (continuousAt_pi.mp firstAligned_continuousAt) 1
  exact hfirst.sub (sliceDot_continuous.continuousAt.smul continuousAt_const)

lemma sliceTargetPerp_continuous : Continuous sliceTargetPerp := by
  exact (sliceTarget_continuous.comp sliceDot_continuous).sub
    (sliceDot_continuous.smul continuous_const)

lemma alignedConfiguration_continuousAt : ContinuousAt alignedConfiguration P := by
  apply continuousAt_pi.mpr
  intro i
  have hpne := sliceTargetPerp_P_ne
  have hab : sliceSourcePerp P + sliceTargetPerp P ≠ 0 := by
    rw [sliceSourcePerp_P]
    exact nonzero_add_self _ hpne
  have h := alignVector_continuousAt (sliceSourcePerp P) (sliceTargetPerp P)
    (firstAligned P i) hab hpne
  have hbase : ContinuousAt (fun Y : Fin 8 → ℝ³ =>
      ((sliceSourcePerp Y, sliceTargetPerp Y), firstAligned Y i)) P :=
    (sliceSourcePerp_continuousAt.prodMk sliceTargetPerp_continuous.continuousAt).prodMk
      ((continuousAt_pi.mp firstAligned_continuousAt) i)
  exact ContinuousAt.comp (f := fun Y : Fin 8 → ℝ³ =>
    ((sliceSourcePerp Y, sliceTargetPerp Y), firstAligned Y i)) h hbase

end SquareAntiprismVerification
