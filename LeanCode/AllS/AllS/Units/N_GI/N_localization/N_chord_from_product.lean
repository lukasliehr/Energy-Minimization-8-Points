import AllS.Units.N_G.N_product_slice
import AllS.Units.N_GI.N_product_gauge.N_chord_stationarity

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem aligned_chord_le_log_product (Y : Fin 8 → Point) (hY : ∀i,‖Y i‖=1)
    (hal : IsProductAligned Y) (hp : 0<productGauge Y) : chordSquare Y≤-2*log (productGauge Y) := by
  have hpos := fun i=>(product_slice_positive_factors Y hal hp i).1
  have he : productGauge Y=∏i,productFactor Y i := by
    rw [productGauge_aligned_value Y hal]
    exact Finset.prod_congr rfl (fun i _=>max_eq_left (hpos i).le)
  have hs := Finset.sum_le_sum (s:=Finset.univ)
    (fun i (_ : i∈(Finset.univ:Finset (Fin 8)))=>Real.log_le_sub_one_of_pos (hpos i))
  rw [←Real.log_prod (fun i _=>(hpos i).ne'),←he] at hs
  rw [chordSquare_correlation Y hY]
  change 16-2*(∑i,productFactor Y i)≤-2*log (productGauge Y)
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hs
  norm_num at hs
  linarith

theorem localization_chord_from_product (Y : Fin 8 → Point) (hY : ∀i,‖Y i‖=1)
    (hp : 0<productGauge Y) :
    ∃(U : Point ≃ₗᵢ[ℝ] Point)(σ : Equiv.Perm (Fin 8)),
      chordSquare (fun i=>U (Y (σ i)))≤-2*log (productGauge Y) ∧
      chordOrbitSquare Y≤chordSquare (fun i=>U (Y (σ i))) := by
  obtain ⟨U,σ,hZ,hal,hg,_⟩ := product_alignment_exists Y hY
  let Z : Fin 8 → Point := fun i=>U (Y (σ i))
  have hpZ : 0<productGauge Z := by rw [hg];exact hp
  refine ⟨U,σ,?_,?_⟩
  · have h := aligned_chord_le_log_product Z hZ hal hpZ
    rwa [hg] at h
  · have hc : Congruent Z Y := ⟨U,σ,fun _=>rfl⟩
    rw [←(gauges_congruence_invariant hc).2]
    exact chordOrbitSquare_le_gaugeChordSquare Z (ContinuousLinearMap.id ℝ Point,Equiv.refl _)
      ⟨fun _=>rfl,Set.mem_univ _⟩

#print axioms localization_chord_from_product
end Blueprint.Thomson.Tail.Implementation
