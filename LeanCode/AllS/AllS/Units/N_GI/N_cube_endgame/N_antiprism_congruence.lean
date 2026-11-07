import AllS.Units.N_GI.N_cube_endgame.N_only_double_active
import AllS.Units.N_GI.N_cube_endgame.N_antiprism_coordinates
import AllS.Units.N_GI.N_product_gauge.N_orbit
import AllS.Units.N_GI.N_upstream_bridge.N_coordinates

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem ordered_cube_antiprism_congruent (e : Fin 3 → Point) (he : Orthonormal ℝ e)
    (label : CubeVertex ≃ Fin 8) :
    Congruent (cubeConfiguration e label packingHeight antiprismCubeQ) (X packingHeight) := by
  obtain ⟨Ue,hUe,_⟩ := Blueprint.Thomson.Finite.congruence_isometry e he
  obtain ⟨Uf,hUf,_⟩ := Blueprint.Thomson.Finite.congruence_isometry cubeHorizontalFrame cubeHorizontalFrame_orthonormal
  let σ : Equiv.Perm (Fin 8) := label.symm.trans cubeModelLabelEquiv.symm
  refine ⟨Uf.trans Ue,σ,fun i => ?_⟩
  change cubeVertexModel e packingHeight antiprismCubeQ (label.symm i)=Ue (Uf (X packingHeight (σ i)))
  rw [cube_antiprism_coordinate_isometry Uf hUf,cubeCanonicalPoint_isometry e Ue hUe]
  congr 1
  change label.symm i=cubeModelLabelEquiv (cubeModelLabelEquiv.symm (label.symm i))
  exact (Equiv.apply_symm_apply cubeModelLabelEquiv (label.symm i)).symm

theorem target_reference_congruent : Congruent (X packingHeight) packingReference := by
  refine ⟨LinearIsometryEquiv.refl ℝ Point,cyclicIndexEquiv.symm,fun i => ?_⟩
  change X packingHeight i=X packingHeight (cyclicIndex (cyclicIndexEquiv.symm i))
  rw [←cyclicIndexEquiv_apply,Equiv.apply_symm_apply]

theorem cube_parameters_antiprism_congruent (e : Fin 3 → Point) (he : Orthonormal ℝ e)
    (label : CubeVertex ≃ Fin 8) (c : ℝ) (q : Fin 3 → ℝ) (hparam : CubeAntiprismParameters c q) :
    Congruent (cubeConfiguration e label c q) packingReference := by
  obtain ⟨rfl,σ,hq⟩ := hparam
  have hnew := ordered_cube_antiprism_congruent (e ∘ σ) (orthonormal_permute e he σ) (cubeAxisLabel label σ)
  have hreindex := cubeConfiguration_reindex_axes e label packingHeight q σ
  rw [hq] at hreindex
  change cubeConfiguration (e ∘ σ) (cubeAxisLabel label σ) packingHeight antiprismCubeQ=
    cubeConfiguration e label packingHeight q at hreindex
  rw [hreindex] at hnew
  exact gauge_congruent_trans hnew target_reference_congruent

theorem cube_endgame_antiprism_congruence (Y : Fin 8 → Point) (hY : IsConfiguration Y)
    (c : ℝ) (hmax : packingMaxInner Y=c) (hc : 0<c) (hcub : c<7/25)
    (hspan : HasSpanningCube (actualContactGraph Y c)) (hmin : PackingLocalMinimum Y) :
    Congruent Y packingReference := by
  obtain ⟨_,e,label,q,he,hq,hrepr,hparam⟩ := cube_endgame_only_double_active Y hY c hmax hc hcub hspan hmin
  rw [hrepr]
  exact cube_parameters_antiprism_congruent e he label c q hparam

#print axioms cube_endgame_antiprism_congruence
end Blueprint.Thomson.Tail.Implementation
