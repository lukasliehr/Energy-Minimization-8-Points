import AllS.Units.N_GI.N_minimizer_exists.N_separation_threshold

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem squaredDistance_continuous (i j : Fin 8) : Continuous (fun Y : Fin 8 → Point => squaredDistance Y i j) := by
  unfold squaredDistance
  fun_prop

theorem separatedConfigurations_compact (ε : ℝ) : IsCompact (separatedConfigurations ε) := by
  have hu : IsCompact {Y : Fin 8 → Point | ∀ i, ‖Y i‖=1} := by
    simpa [Set.pi,Metric.mem_sphere,dist_zero_right] using
      (isCompact_univ_pi (fun _ : Fin 8 => isCompact_sphere (0:Point) 1))
  have hc : IsClosed {Y : Fin 8 → Point | ∀ i j, i ≠ j → ε ≤ squaredDistance Y i j} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter (fun i => isClosed_iInter (fun j => isClosed_iInter (fun _ =>
      isClosed_le continuous_const (squaredDistance_continuous i j))))
  exact hu.inter_right hc

theorem separatedConfigurations_configuration (ε : ℝ) (he : 0 < ε)
    (Y : Fin 8 → Point) (hY : Y ∈ separatedConfigurations ε) : IsConfiguration Y := by
  refine ⟨hY.1,?_⟩
  intro i j hij
  by_contra hne
  have hd := hY.2 i j hne
  simp [squaredDistance,hij] at hd
  linarith

theorem minimizer_exists_compact_set (p : ℝ) (Z : Fin 8 → Point) (hp : 0 < p)
    (hZ : IsConfiguration Z) :
    Z ∈ separatedConfigurations (separationThreshold p Z) ∧
      IsCompact (separatedConfigurations (separationThreshold p Z)) := by
  have hs := (minimizer_exists_separation_threshold p Z hp hZ).2.2.2
  exact ⟨⟨hZ.1,fun i j hij => (hs i j hij).le⟩,separatedConfigurations_compact _⟩

#check minimizer_exists_compact_set
#print axioms minimizer_exists_compact_set
end Blueprint.Thomson.Tail.Implementation
