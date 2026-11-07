import AllS.Units.N_FI.N_cell_soundness.N_congruence_energy
import AllS.Units.N_FI.N_odd_image.N_extract
import AllS.Units.N_F.N_congruence

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

theorem certificate_equality_allowed_contacts {s a : ℝ} {D : ℕ} {m : Fin 5 → ℕ}
    (h : Certificate s a D m) (Y : Configuration) (hY : IsConfiguration Y)
    (he : E s Y=E s (X a)) : AllowedContacts a Y := by
  intro i j hij
  have hn : Y i≠Y j := fun heq => hij (hY.2 heq)
  have hd := (geometry_distance_domain (Y i) (Y j) (hY.1 i) (hY.1 j) hn).1
  have hz := equality_pair_gaps_zero h Y hY he i j hij
  have hg : (hermitePolynomial s a m).eval (inner ℝ (Y i) (Y j))=phi s (inner ℝ (Y i) (Y j)) := by
    change phi s (inner ℝ (Y i) (Y j))-(hermitePolynomial s a m).eval (inner ℝ (Y i) (Y j))=0 at hz
    linarith
  obtain ⟨r,hr,hrv⟩ := ((hermite_minorant s a D m h.s_nonneg h.physical_a h.profile_valid).1 _ hd.1 hd.2).2.mp hg
  fin_cases r
  · exact Or.inl hrv
  · exact Or.inr ⟨3,hrv.symm⟩
  · exact Or.inr ⟨1,hrv.symm⟩
  · exact Or.inr ⟨2,hrv.symm⟩
  · exact Or.inr ⟨0,hrv.symm⟩

theorem cell_soundness_uniqueness (s a : ℝ) (D : ℕ) (m : Fin 5 → ℕ)
    (h : Certificate s a D m) : IsUniqueMinimizer s (X a) := by
  refine ⟨candidate_is_configuration a (physical_mem_Ioo a h.physical_a),?_⟩
  intro Y hY
  refine ⟨energy_lower_energy_bound s a D m h Y hY,?_⟩
  constructor
  · intro he
    exact odd_moment_congruence a Y h.physical_a hY
      (certificate_equality_allowed_contacts h Y hY he) (certificate_vertex_odd_moments h Y hY he)
  · exact cell_soundness_congruence_energy s Y (X a)

#check cell_soundness_uniqueness
#print axioms cell_soundness_uniqueness
end Blueprint.Thomson.Finite
