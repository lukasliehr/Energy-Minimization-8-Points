import AllS.Units.N_FI.N_cell_soundness.N_uniqueness

namespace Blueprint.Thomson.Finite

/-- Soundness of the concrete all-s finite certificate, with the exact target
energy, configuration and orthogonal-congruence definitions. -/
theorem certificate_soundness (s a : ℝ) (D : ℕ) (profile : Fin 5 → ℕ)
    (h : Certificate s a D profile) : IsUniqueMinimizer s (X a) :=
  cell_soundness_uniqueness s a D profile h

#check certificate_soundness
#print axioms certificate_soundness
end Blueprint.Thomson.Finite
