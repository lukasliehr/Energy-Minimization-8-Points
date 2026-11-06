import AllS.Units.N_GI.N_product_gauge.N_continuous_extrema

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem gauge_congruent_symm {Y Z : Fin 8 → Point} (h : Congruent Y Z) : Congruent Z Y := by
  obtain ⟨U,σ,h⟩ := h
  refine ⟨U.symm,σ.symm,fun i => ?_⟩
  rw [h (σ.symm i),Equiv.apply_symm_apply,U.symm_apply_apply]

theorem gauge_congruent_trans {Y Z W : Fin 8 → Point}
    (h : Congruent Y Z) (h' : Congruent Z W) : Congruent Y W := by
  obtain ⟨U,σ,h⟩ := h
  obtain ⟨V,τ,h'⟩ := h'
  exact ⟨V.trans U,σ.trans τ,fun i => (h i).trans (congrArg U (h' (σ i)))⟩

theorem alignedConfiguration_range (Y : Fin 8 → Point) :
    alignedConfiguration Y '' gaugeActions={Z | Congruent Z Y} := by
  ext Z
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨gaugeOrthogonalEquiv a.1 ha.1,a.2,fun _ => rfl⟩
  · rintro ⟨U,σ,h⟩
    exact ⟨(U.toLinearIsometry.toContinuousLinearMap,σ),⟨U.norm_map,Set.mem_univ _⟩,funext (fun i => (h i).symm)⟩

theorem congruence_orbit_eq {Y Z : Fin 8 → Point} (h : Congruent Y Z) :
    {W | Congruent W Y}={W | Congruent W Z} := by
  ext W
  exact ⟨fun h' => gauge_congruent_trans h' h,fun h' => gauge_congruent_trans h' (gauge_congruent_symm h)⟩

theorem gaugeProduct_image_eq (Y : Fin 8 → Point) :
    gaugeProduct Y '' gaugeActions=
      (fun Z : Fin 8 → Point => ∏i,max (inner ℝ (packingReference i) (Z i)) 0) '' {Z | Congruent Z Y} := by
  rw [←alignedConfiguration_range Y,Set.image_image]
  rfl

theorem gaugeChordSquare_image_eq (Y : Fin 8 → Point) :
    gaugeChordSquare Y '' gaugeActions=
      (fun Z : Fin 8 → Point => ∑i,‖Z i-packingReference i‖^2) '' {Z | Congruent Z Y} := by
  rw [←alignedConfiguration_range Y,Set.image_image]
  rfl

theorem gauges_congruence_invariant {Y Z : Fin 8 → Point} (h : Congruent Y Z) :
    productGauge Y=productGauge Z ∧ chordOrbitSquare Y=chordOrbitSquare Z := by
  unfold productGauge chordOrbitSquare
  rw [gaugeProduct_image_eq,gaugeProduct_image_eq,gaugeChordSquare_image_eq,gaugeChordSquare_image_eq,congruence_orbit_eq h]
  exact ⟨rfl,rfl⟩

#print axioms gauges_congruence_invariant
end Blueprint.Thomson.Tail.Implementation
