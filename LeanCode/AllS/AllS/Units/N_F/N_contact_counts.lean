import AllS.Units.N_FI.N_contact_counts.N_vertex_counts

namespace Blueprint.Thomson.Finite

theorem vertex_contact_counts (a : ℝ) (ha : physical a) :
    (∀ n : Fin 4 → ℕ, (∑ i, n i)=7 →
      1+(∑ i, (n i:ℝ)*contacts a i)=0 →
      1+(∑ i, (n i:ℝ)*(contacts a i)^3)=0 → n=baselineCounts) ∧
    (∀ Y : Fin 8 → Point, IsConfiguration Y → AllowedContacts a Y →
      (∀ i, (∑ j, inner ℝ (Y i) (Y j))=0 ∧ (∑ j, (inner ℝ (Y i) (Y j))^3)=0) →
      ∀ i, vertexContactCounts a Y i=baselineCounts) :=
  ⟨contact_counts_sign_integer_cases a ha,fun Y => contact_counts_vertex_counts a Y ha⟩

#check vertex_contact_counts
#print axioms vertex_contact_counts
end Blueprint.Thomson.Finite
