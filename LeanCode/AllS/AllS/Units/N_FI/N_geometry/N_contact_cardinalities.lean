import AllS.Units.N_FI.N_geometry.N_gram_entries

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite

def candidateNeighborLabels (i : Fin 8) (r : Fin 4) : Finset (Fin 8) :=
  Finset.univ.filter (fun j => i ≠ j ∧ candidateContactLabel i j = r)

def candidatePairLabels (r : Fin 4) : Finset (Fin 8 × Fin 8) :=
  Finset.univ.filter (fun p => p.1 < p.2 ∧ candidateContactLabel p.1 p.2 = r)

def candidateTriangleLabels (i j k : Fin 8) : Fin 3 → Fin 4 :=
  ![candidateContactLabel i j, candidateContactLabel i k, candidateContactLabel j k]

def candidateTriangleOrbit (r : Fin 5) : Finset (Fin 8 × Fin 8 × Fin 8) :=
  Finset.univ.filter (fun p => p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧
    candidateTriangleLabels p.1 p.2.1 p.2.2 ∈ contactLabelOrbit r)

def candidateNeighborCount : Fin 4 → ℕ := ![2,1,2,2]
def candidatePairCount : Fin 4 → ℕ := ![8,4,8,8]
def candidateTriangleCount : Fin 5 → ℕ := ![8,8,8,16,16]

def candidateNeighbors (a : ℝ) (i : Fin 8) (r : Fin 4) : Finset (Fin 8) :=
  Finset.univ.filter (fun j => i ≠ j ∧ inner ℝ (X a i) (X a j) = contacts a r)

def candidatePairs (a : ℝ) (r : Fin 4) : Finset (Fin 8 × Fin 8) :=
  Finset.univ.filter (fun p => p.1 < p.2 ∧ inner ℝ (X a p.1) (X a p.2) = contacts a r)

def candidateRealTriangle (a : ℝ) (i j k : Fin 8) : Fin 3 → ℝ :=
  ![inner ℝ (X a i) (X a j), inner ℝ (X a i) (X a k), inner ℝ (X a j) (X a k)]

def candidateTriangles (a : ℝ) (r : Fin 5) : Finset (Fin 8 × Fin 8 × Fin 8) :=
  Finset.univ.filter (fun p => p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧
    candidateRealTriangle a p.1 p.2.1 p.2.2 ∈ contactRealOrbit a r)

def ContactCardinalityContract : Prop := ∀ a : ℝ, physical a →
  Function.Injective (X a) ∧
  (∀ i r, (candidateNeighbors a i r).card = candidateNeighborCount r) ∧
  (∀ r, (candidatePairs a r).card = candidatePairCount r) ∧
  (∀ r, (candidateTriangles a r).card = candidateTriangleCount r)


theorem candidateNeighborLabels_card : ∀ i r,
    (candidateNeighborLabels i r).card = candidateNeighborCount r := by decide

theorem candidatePairLabels_card : ∀ r,
    (candidatePairLabels r).card = candidatePairCount r := by decide

theorem candidateTriangleOrbit_card : ∀ r,
    (candidateTriangleOrbit r).card = candidateTriangleCount r := by decide

theorem candidateNeighbors_eq_labels (a : ℝ) (ha : physical a) (i : Fin 8) (r : Fin 4) :
    candidateNeighbors a i r = candidateNeighborLabels i r := by
  classical
  ext j
  by_cases hij : i = j
  · simp [candidateNeighbors,candidateNeighborLabels,hij]
  · simp [candidateNeighbors,candidateNeighborLabels,candidate_gram_entry a ha,hij,
      (contacts_injective a ha).eq_iff]

theorem candidatePairs_eq_labels (a : ℝ) (ha : physical a) (r : Fin 4) :
    candidatePairs a r = candidatePairLabels r := by
  classical
  ext p
  by_cases hp : p.1 < p.2
  · simp [candidatePairs,candidatePairLabels,candidate_gram_entry a ha,hp,ne_of_lt hp,
      (contacts_injective a ha).eq_iff]
  · simp [candidatePairs,candidatePairLabels,hp]

theorem candidateRealTriangle_eq (a : ℝ) (ha : physical a) (i j k : Fin 8)
    (hij : i < j) (hjk : j < k) :
    candidateRealTriangle a i j k = contactTripleEval a (candidateTriangleLabels i j k) := by
  funext r
  fin_cases r <;> simp [candidateRealTriangle, contactTripleEval, candidateTriangleLabels,
    candidate_gram_entry a ha, ne_of_lt hij, ne_of_lt hjk, ne_of_lt (lt_trans hij hjk)]

theorem candidateTriangles_eq_labels (a : ℝ) (ha : physical a) (r : Fin 5) :
    candidateTriangles a r = candidateTriangleOrbit r := by
  classical
  ext p
  by_cases hp : p.1 < p.2.1 ∧ p.2.1 < p.2.2
  · simp [candidateTriangles,candidateTriangleOrbit,hp.1,hp.2,
      candidateRealTriangle_eq a ha p.1 p.2.1 p.2.2 hp.1 hp.2,contactRealOrbit,
      (contactTripleEval_injective a ha).eq_iff]
  · simp only [candidateTriangles,candidateTriangleOrbit,Finset.mem_filter,
      Finset.mem_univ,true_and]
    tauto

theorem geometry_contact_cardinalities : ContactCardinalityContract := by
  intro a ha
  refine ⟨(candidate_is_configuration a (physical_mem_Ioo a ha)).2, ?_, ?_, ?_⟩
  · intro i r
    rw [candidateNeighbors_eq_labels a ha]
    exact candidateNeighborLabels_card i r
  · intro r
    rw [candidatePairs_eq_labels a ha]
    exact candidatePairLabels_card r
  · intro r
    rw [candidateTriangles_eq_labels a ha]
    exact candidateTriangleOrbit_card r

#check geometry_contact_cardinalities
#print axioms geometry_contact_cardinalities

#check ContactCardinalityContract
#print axioms ContactCardinalityContract
end Blueprint.Thomson.Finite
