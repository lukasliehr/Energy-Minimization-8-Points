import AllS.Units.N_GI.N_product_gauge.N_orbit
import AllS.Units.N_GI.N_nearest_chart.N_tangent

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem alignedConfiguration_norm (Y : Fin 8 → Point) (hY : ∀i,‖Y i‖=1)
    (a : GaugeAction) (ha : a∈gaugeActions) (i : Fin 8) : ‖alignedConfiguration Y a i‖=1 :=
  (ha.1 _).trans (hY _)

theorem gauge_factor_bounds (Y : Fin 8 → Point) (hY : ∀i,‖Y i‖=1)
    (a : GaugeAction) (ha : a∈gaugeActions) (i : Fin 8) :
    0≤ max (inner ℝ (packingReference i) (alignedConfiguration Y a i)) 0 ∧
    max (inner ℝ (packingReference i) (alignedConfiguration Y a i)) 0≤1 := by
  refine ⟨le_max_right _ _,max_le ?_ (by norm_num)⟩
  have hh := real_inner_le_norm (packingReference i) (alignedConfiguration Y a i)
  simpa only [packingReference_norm,alignedConfiguration_norm Y hY a ha,one_mul] using hh

theorem productGauge_bounds (Y : Fin 8 → Point) (hY : ∀i,‖Y i‖=1) :
    0≤productGauge Y ∧ productGauge Y≤1 := by
  obtain ⟨a,ha,he,hm⟩ := (product_gauge_attained_extrema Y).1
  rw [he]
  exact ⟨Finset.prod_nonneg (fun i _ => (gauge_factor_bounds Y hY a ha i).1),
    Finset.prod_le_one (fun i _ => (gauge_factor_bounds Y hY a ha i).1)
      (fun i _ => (gauge_factor_bounds Y hY a ha i).2)⟩

theorem gaugeProduct_le_factor (Y : Fin 8 → Point) (hY : ∀i,‖Y i‖=1)
    (a : GaugeAction) (ha : a∈gaugeActions) (i : Fin 8) :
    gaugeProduct Y a≤ max (inner ℝ (packingReference i) (alignedConfiguration Y a i)) 0 := by
  simpa only [gaugeProduct,Finset.prod_singleton] using Finset.prod_le_prod_of_subset_of_le_one (Finset.subset_univ ({i} : Finset (Fin 8)))
    (fun j _ => (gauge_factor_bounds Y hY a ha j).1)
    (fun j _ _ => (gauge_factor_bounds Y hY a ha j).2)

theorem productGauge_eq_one_iff (Y : Fin 8 → Point) (hY : ∀i,‖Y i‖=1) :
    productGauge Y=1 ↔ Congruent Y packingReference := by
  constructor
  · intro he
    obtain ⟨a,ha,hprod,hm⟩ := (product_gauge_attained_extrema Y).1
    have halign : alignedConfiguration Y a=packingReference := by
      funext i
      have hfac : max (inner ℝ (packingReference i) (alignedConfiguration Y a i)) 0=1 :=
        le_antisymm (gauge_factor_bounds Y hY a ha i).2
          (by simpa only [←hprod,he] using gaugeProduct_le_factor Y hY a ha i)
      have hpos : 0 < inner ℝ (packingReference i) (alignedConfiguration Y a i) := by
        by_contra hn
        rw [max_eq_right (le_of_not_gt hn)] at hfac
        norm_num at hfac
      rw [max_eq_left hpos.le] at hfac
      have hd := norm_sub_sq_real (packingReference i) (alignedConfiguration Y a i)
      rw [packingReference_norm,alignedConfiguration_norm Y hY a ha,hfac] at hd
      have hn : ‖packingReference i-alignedConfiguration Y a i‖=0 := by nlinarith [norm_nonneg (packingReference i-alignedConfiguration Y a i)]
      exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm
    apply gauge_congruent_symm
    change packingReference∈{Z | Congruent Z Y}
    rw [←alignedConfiguration_range Y]
    exact ⟨a,ha,halign⟩
  · intro h
    have hp : packingReference∈alignedConfiguration Y '' gaugeActions := by
      rw [alignedConfiguration_range]
      exact gauge_congruent_symm h
    obtain ⟨a,ha,he⟩ := hp
    have hone : gaugeProduct Y a=1 := by
      unfold gaugeProduct
      simp only [he,real_inner_self_eq_norm_sq,packingReference_norm,one_pow,max_eq_left (show (0:ℝ)≤1 by norm_num),Finset.prod_const_one]
    exact le_antisymm (productGauge_bounds Y hY).2 (hone ▸ gaugeProduct_le_productGauge Y a ha)

theorem product_gauge_invariant_and_one (Y : Fin 8 → Point) (hY : ∀i,‖Y i‖=1) :
    (∀Z,Congruent Y Z → productGauge Y=productGauge Z ∧ chordOrbitSquare Y=chordOrbitSquare Z) ∧
    0≤productGauge Y ∧ productGauge Y≤1 ∧ (productGauge Y=1 ↔ Congruent Y packingReference) :=
  ⟨fun _ h => gauges_congruence_invariant h,(productGauge_bounds Y hY).1,
    (productGauge_bounds Y hY).2,productGauge_eq_one_iff Y hY⟩

#print axioms product_gauge_invariant_and_one
end Blueprint.Thomson.Tail.Implementation
