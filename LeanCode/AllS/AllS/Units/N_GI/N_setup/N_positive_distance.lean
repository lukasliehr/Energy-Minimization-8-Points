import AllS.Units.N_GI.N_setup.N_pairs

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem setup_positive_distance (Y : Fin 8 → Point) (hY : IsConfiguration Y)
    (i j : Fin 8) (hij : i ≠ j) : 0 < squaredDistance Y i j := by
  have hne : Y i - Y j ≠ 0 := sub_ne_zero.mpr (fun h => hij (hY.2 h))
  exact sq_pos_of_pos (norm_pos_iff.mpr hne)

theorem squaredDistance_nonneg (Y : Fin 8 → Point) (i j : Fin 8) :
    0 ≤ squaredDistance Y i j := sq_nonneg _

#print axioms setup_positive_distance
end Blueprint.Thomson.Tail.Implementation
