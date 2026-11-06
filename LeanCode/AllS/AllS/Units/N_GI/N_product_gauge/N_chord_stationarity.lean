import AllS.Units.N_G.N_product_gauge
import AllS.Units.N_GI.N_product_gauge.N_axis_rotation
import AllS.Units.N_GI.N_nearest_chart.N_positive_roots

noncomputable section
open SquareAntiprismVerification Filter
namespace Blueprint.Thomson.Tail.Implementation

def gaugeActionCompose (a b : GaugeAction) : GaugeAction := (a.1.comp b.1,a.2.trans b.2)

theorem gaugeActionCompose_mem (a b : GaugeAction) (ha : a∈gaugeActions) (hb : b∈gaugeActions) :
    gaugeActionCompose a b∈gaugeActions :=
  ⟨fun x => (ha.1 (b.1 x)).trans (hb.1 x),Set.mem_univ _⟩

theorem alignedConfiguration_comp (Y : Fin 8 → Point) (a b : GaugeAction) :
    alignedConfiguration (alignedConfiguration Y b) a=alignedConfiguration Y (gaugeActionCompose a b) := rfl

def IsChordAligned (Y : Fin 8 → Point) : Prop :=
  ∀a∈gaugeActions,chordSquare Y≤gaugeChordSquare Y a

theorem attained_chord_alignment (Y : Fin 8 → Point) (a : GaugeAction) (ha : a∈gaugeActions)
    (hmin : ∀b∈gaugeActions,gaugeChordSquare Y a≤gaugeChordSquare Y b) :
    IsChordAligned (alignedConfiguration Y a) := by
  intro b hb
  exact hmin (gaugeActionCompose b a) (gaugeActionCompose_mem b a hb ha)

theorem chordSquare_correlation (Y : Fin 8 → Point) (hY : ∀i,‖Y i‖=1) :
    chordSquare Y=16-2*∑i,inner ℝ (packingReference i) (Y i) := by
  unfold chordSquare
  calc
    _=∑i,(2-2*inner ℝ (packingReference i) (Y i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_sub_sq_real,hY i,packingReference_norm i,real_inner_comm]
      ring
    _=16-2*∑i,inner ℝ (packingReference i) (Y i) := by
      rw [Finset.sum_sub_distrib,←Finset.mul_sum]
      norm_num

theorem chord_alignment_cross_zero (Y : Fin 8 → Point) (hY : ∀i,‖Y i‖=1)
    (hmin : IsChordAligned Y) : (∑i,crossVec (packingReference i) (Y i))=0 := by
  ext k
  let f : ℝ → ℝ := fun t => ∑i,inner ℝ (packingReference i) (axisRotate k t (Y i))
  have hf : HasDerivAt f (∑i,-(crossVec (packingReference i) (Y i)) k) 0 :=
    HasDerivAt.fun_sum (fun i _ => axisRotate_inner_hasDerivAt k (packingReference i) (Y i))
  have hmax : IsLocalMax f 0 := by
    apply Filter.Eventually.of_forall
    intro t
    have hm := hmin (axisRotationOperator k t,Equiv.refl _) ⟨axisRotationOperator_mem k t,Set.mem_univ _⟩
    change chordSquare Y≤chordSquare (fun i => axisRotate k t (Y i)) at hm
    rw [chordSquare_correlation Y hY,chordSquare_correlation _ (fun i => (axisRotate_norm k t (Y i)).trans (hY i))] at hm
    change f t≤f 0
    have h0 : f 0=∑i,inner ℝ (packingReference i) (Y i) := by simp [f]
    rw [h0]
    linarith
  have hz := hmax.hasDerivAt_eq_zero hf
  simpa only [Finset.sum_neg_distrib,neg_eq_zero,WithLp.ofLp_sum,Finset.sum_apply,PiLp.zero_apply] using hz

theorem chord_alignment_exists (Y : Fin 8 → Point) (hY : ∀i,‖Y i‖=1) :
    ∃(U : Point ≃ₗᵢ[ℝ] Point)(σ : Equiv.Perm (Fin 8)),
      let Z : Fin 8 → Point := fun i => U (Y (σ i))
      (∀i,‖Z i‖=1) ∧ chordSquare Z=chordOrbitSquare Y ∧ IsChordAligned Z ∧
      (∑i,crossVec (packingReference i) (Z i))=0 := by
  obtain ⟨a,ha,he,hm⟩ := (product_gauge_attained_extrema Y).2
  have hn := alignedConfiguration_norm Y hY a ha
  have hal := attained_chord_alignment Y a ha hm
  exact ⟨gaugeOrthogonalEquiv a.1 ha.1,a.2,hn,he.symm,hal,chord_alignment_cross_zero _ hn hal⟩

#print axioms chord_alignment_exists
end Blueprint.Thomson.Tail.Implementation
