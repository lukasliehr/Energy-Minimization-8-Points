import AllS.Units.N_GI.N_minimizer_exists.N_strict_separation_at_minimum

noncomputable section
open Filter
namespace Blueprint.Thomson.Tail.Implementation

theorem configuration_eventually_of_curve (Y : Fin 8 → Point) (hY : IsConfiguration Y)
    (γ : ℝ → Fin 8 → Point) (hγ0 : γ 0=Y)
    (hcont : ∀ i, ContinuousAt (fun t => γ t i) 0)
    (hunit : ∀ᶠ t in nhds (0:ℝ), ∀ i, ‖γ t i‖=1) :
    ∀ᶠ t in nhds (0:ℝ), IsConfiguration (γ t) := by
  have hpair (i j : Fin 8) : ∀ᶠ t in nhds (0:ℝ), i ≠ j → γ t i ≠ γ t j := by
    by_cases hij : i=j
    · exact Filter.Eventually.of_forall (by intro t h; exact (h hij).elim)
    · have hc := ((hcont i).sub (hcont j)).norm
      have hp : 0 < ‖γ 0 i-γ 0 j‖ := by
        rw [hγ0]
        exact norm_pos_iff.mpr (sub_ne_zero.mpr (hY.2.ne hij))
      have hn := hc.eventually (isOpen_Ioi.mem_nhds hp)
      filter_upwards [hn] with t ht
      exact fun _ => sub_ne_zero.mp (norm_pos_iff.mp ht)
  have hall : ∀ᶠ t in nhds (0:ℝ), ∀ i j, i ≠ j → γ t i ≠ γ t j :=
    Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hpair i))
  filter_upwards [hunit,hall] with t hu ht
  refine ⟨hu,?_⟩
  intro i j he
  by_contra hne
  exact ht i j hne he

theorem squaredEnergy_curve_differentiable (p : ℝ) (Y : Fin 8 → Point) (hY : IsConfiguration Y)
    (γ : ℝ → Fin 8 → Point) (hγ0 : γ 0=Y)
    (hdiff : ∀ i, DifferentiableAt ℝ (fun t => γ t i) 0) :
    DifferentiableAt ℝ (fun t => squaredEnergy p (γ t)) 0 := by
  unfold squaredEnergy
  apply DifferentiableAt.fun_sum
  intro i _
  apply DifferentiableAt.fun_sum
  intro j hj
  have hd := ((hdiff i).sub (hdiff j)).norm_sq ℝ
  apply hd.rpow_const
  left
  change squaredDistance (γ 0) i j ≠ 0
  rw [hγ0]
  exact (setup_positive_distance Y hY i j (ne_of_lt (Finset.mem_filter.mp hj).2)).ne'

theorem minimizer_exists_stationarity (p : ℝ) (Y : Fin 8 → Point) (hY : IsConfiguration Y)
    (hmin : ∀ W, IsConfiguration W → squaredEnergy p Y ≤ squaredEnergy p W) : Stationary p Y := by
  intro γ hγ0 hdiff hunit
  have hcfg := configuration_eventually_of_curve Y hY γ hγ0 (fun i => (hdiff i).continuousAt) hunit
  have hlocal : IsLocalMin (fun t => squaredEnergy p (γ t)) 0 := by
    filter_upwards [hcfg] with t ht
    rw [hγ0]
    exact hmin _ ht
  have hd := (squaredEnergy_curve_differentiable p Y hY γ hγ0 hdiff).hasDerivAt
  have hz := hlocal.hasDerivAt_eq_zero hd
  rw [hz] at hd
  exact hd

#check minimizer_exists_stationarity
#print axioms minimizer_exists_stationarity
end Blueprint.Thomson.Tail.Implementation
