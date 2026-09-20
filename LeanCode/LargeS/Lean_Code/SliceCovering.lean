import Lean_Code.SliceAlignment
import Lean_Code.PackingGeometry

open Real Filter
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Every sufficiently nearby sphere tuple has arbitrarily small gauge
coordinates after a common orthogonal transformation. -/
theorem local_chart_covering (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Y : Fin 8 → ℝ³,
      (∀ i, ‖Y i‖ = 1) → dist Y P < δ →
      ∃ q : InfinitesimalCoordinates, InContactGauge q ∧ ‖q‖ < ε ∧
        Congruent Y (coordinateChart q) := by
  have hrad : aInf ^ 2 < sliceTargetDen := by
    unfold sliceTargetDen
    linarith [aInf_mem_Ioo.2]
  have hdot : ∀ᶠ Y in nhds P, sliceDot Y ^ 2 < sliceTargetDen := by
    have hc : ContinuousAt (fun Y => sliceDot Y ^ 2) P := sliceDot_continuous.continuousAt.pow 2
    have hv : sliceDot P ^ 2 < sliceTargetDen := by rw [sliceDot_P]; exact hrad
    exact hc.tendsto.eventually (eventually_lt_nhds hv)
  have hcoords : ContinuousAt (fun Y => coordinateInverse (alignedConfiguration Y)) P :=
    ContinuousAt.comp (f := alignedConfiguration)
      coordinateInverse_continuous.continuousAt alignedConfiguration_continuousAt
  have hcoordsmall : ∀ᶠ Y in nhds P, ‖coordinateInverse (alignedConfiguration Y)‖ < ε := by
    have hcenter : ‖coordinateInverse (alignedConfiguration P)‖ < ε := by
      rw [alignedConfiguration_P, coordinateInverse_P, norm_zero]
      exact hε
    exact hcoords.norm.tendsto.eventually (eventually_lt_nhds hcenter)
  have hside : ∀ i : Fin 8, ∀ᶠ Y in nhds P,
      0 < inner ℝ (alignedConfiguration Y i) (polarP i) := by
    intro i
    have hc : ContinuousAt (fun Y => inner ℝ (alignedConfiguration Y i) (polarP i)) P :=
      ((continuousAt_pi.mp alignedConfiguration_continuousAt) i).inner continuousAt_const
    have hcenter : 0 < inner ℝ (alignedConfiguration P i) (polarP i) := by
      rw [alignedConfiguration_P, P_eq_polarP]
      simp [polarP_norm]
    exact hc.tendsto.eventually (eventually_gt_nhds hcenter)
  have hall : ∀ᶠ Y in nhds P,
      sliceDot Y ^ 2 < sliceTargetDen ∧ ‖coordinateInverse (alignedConfiguration Y)‖ < ε ∧
      ∀ i, 0 < inner ℝ (alignedConfiguration Y i) (polarP i) :=
    hdot.and (hcoordsmall.and (Filter.eventually_all.mpr hside))
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨δ, hδ, ?_⟩
  intro Y hY hdist
  obtain ⟨hd, hn, hs⟩ := hnear hdist
  refine ⟨coordinateInverse (alignedConfiguration Y), alignedConfiguration_gauge Y hY hd.le, hn, ?_⟩
  rw [coordinateChart_inverse _ (alignedConfiguration_sphere Y hY) (fun i => (hs i).le)]
  exact alignedConfiguration_congruent Y

lemma congruent_refl (Y : Fin 8 → ℝ³) : Congruent Y Y := by
  exact ⟨LinearIsometryEquiv.refl ℝ _, Equiv.refl _, fun i => rfl⟩

lemma congruent_trans {X Y Z : Fin 8 → ℝ³} (hXY : Congruent X Y) (hYZ : Congruent Y Z) :
    Congruent X Z := by
  obtain ⟨U, f, hf⟩ := hXY
  obtain ⟨V, g, hg⟩ := hYZ
  refine ⟨U.trans V, g.trans f, ?_⟩
  intro i
  change Z i = V (U (X (f (g i))))
  rw [hg, hf]

lemma congruent_symm {X Y : Fin 8 → ℝ³} (hXY : Congruent X Y) : Congruent Y X := by
  obtain ⟨U, f, hf⟩ := hXY
  refine ⟨U.symm, f.symm, ?_⟩
  intro i
  rw [hf]
  simp

lemma congruent_isConfiguration {X Y : Fin 8 → ℝ³} (hXY : Congruent X Y)
    (hX : IsConfiguration X) : IsConfiguration Y := by
  obtain ⟨Q, σ, hQ⟩ := hXY
  refine ⟨?_, ?_⟩
  · intro i
    change ‖Y i‖ = 1
    rw [hQ, Q.norm_map]
    exact hX.1 (σ i)
  · intro i j hij
    apply σ.injective
    apply hX.2
    apply Q.injective
    simpa only [← hQ] using hij

def SmallChartRepresentable (ε : ℝ) (Z : SphereTuple) : Prop :=
  ∃ q : InfinitesimalCoordinates, InContactGauge q ∧ ‖q‖ < ε ∧
    Congruent (fromSphereTuple Z) (coordinateChart q)

theorem chart_orbit_neighborhood (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set SphereTuple, IsOpen U ∧ OrbitNeighborhood U ∧
      ∀ Z ∈ U, SmallChartRepresentable ε Z := by
  let S : Set SphereTuple := {Z | SmallChartRepresentable ε Z}
  refine ⟨interior S, isOpen_interior, ?_, fun Z hZ => show Z ∈ S from interior_subset hZ⟩
  obtain ⟨δ, hδ, hcover⟩ := local_chart_covering ε hε
  intro Y hY hcong
  obtain ⟨Q, σ, hQ⟩ := hcong
  let T : SphereTuple → (Fin 8 → ℝ³) := fun Z i => Q (fromSphereTuple Z (σ i))
  have hT : Continuous T := by
    unfold T fromSphereTuple
    fun_prop
  have hTY : T (toSphereTuple Y hY) = P := by
    funext i
    exact (hQ i).symm
  have hUopen : IsOpen (T ⁻¹' Metric.ball P δ) := Metric.isOpen_ball.preimage hT
  have hmem : toSphereTuple Y hY ∈ T ⁻¹' Metric.ball P δ := by
    change dist (T (toSphereTuple Y hY)) P < δ
    rw [hTY, dist_self]
    exact hδ
  apply mem_interior.mpr
  refine ⟨T ⁻¹' Metric.ball P δ, ?_, hUopen, hmem⟩
  intro Z hZ
  have hsphere : ∀ i, ‖T Z i‖ = 1 := by
    intro i
    exact (Q.norm_map _).trans (fromSphereTuple_sphere Z (σ i))
  obtain ⟨q, hqg, hqn, hqc⟩ := hcover (T Z) hsphere hZ
  refine ⟨q, hqg, hqn, congruent_trans ?_ hqc⟩
  exact ⟨Q, σ, fun i => rfl⟩

end SquareAntiprismVerification
