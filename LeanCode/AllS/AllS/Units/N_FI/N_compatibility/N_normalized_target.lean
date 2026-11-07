import AllS.Units.N_F.N_compatibility
import AllS.Units.N_FI.N_raw_projection.N_target_directions

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

theorem hermitePolynomial_natDegree_le (s a : ℝ) (D : ℕ) (m : Fin 5 → ℕ)
    (hm : Profile.Valid D m) : (hermitePolynomial s a m).natDegree≤D := by
  by_cases hz : hermitePolynomial s a m=0
  · simp [hz]
  · apply Nat.le_of_lt_succ
    apply (Polynomial.natDegree_lt_iff_degree_lt hz).mpr
    simpa only [hm.1] using hermitePolynomial_degree s a m

/-- The exact Hermite target lies in the same compatible polynomial space as
every Gram polynomial, whenever the height solves the stationarity equation. -/
theorem normalizedTarget_compatible (s a β : ℝ) (D : ℕ) (m : Fin 5 → ℕ)
    (hs : 0 ≤ s) (ha : physical a) (hroot : F s a = 0) (hm : Profile.Valid D m) :
    normalizedTarget s a β m ∈ Compatible a D := by
  have hb := (mem_boundedSymmetric D _).mp
    (boundedNormalizedPolynomial D (hermitePolynomial s a m)
      (hermitePolynomial_natDegree_le s a D m hm) β (Ehat s (X a))).property
  apply (mem_Compatible a D _).mpr
  exact ⟨hb.1,hb.2,compatibility_target_annihilation s a D m hs ha hroot hm β⟩

#print axioms hermitePolynomial_natDegree_le
#print axioms normalizedTarget_compatible
end Blueprint.Thomson.Finite
