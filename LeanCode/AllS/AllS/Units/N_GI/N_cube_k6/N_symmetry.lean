import AllS.Units.N_GI.N_auxiliary_graphs.N_assemble

set_option maxHeartbeats 3000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

def sameTriangleIndex (i j : Fin 8) : Prop := i.val<6 ∧ j.val<6 ∧ i.val/3=j.val/3
instance (i j : Fin 8) : Decidable (sameTriangleIndex i j) := inferInstanceAs
  (Decidable (i.val<6 ∧ j.val<6 ∧ i.val/3=j.val/3))

/-- Four relative positions of an unordered pair with respect to two disjoint triples. -/
theorem triangle_pair_normalization (x y : Fin 8) (hxy : x≠y) :
    ∃ (e : Equiv.Perm (Fin 8)) (a b : Fin 8),
      ((a=0 ∧ b=1) ∨ (a=0 ∧ b=3) ∨ (a=0 ∧ b=6) ∨ (a=6 ∧ b=7)) ∧
      (∀i,(e i=x ∨ e i=y) ↔ (i=a ∨ i=b)) ∧
      (∀i,(e i).val<6 ↔ i.val<6) ∧
      (∀i j,sameTriangleIndex (e i) (e j) ↔ sameTriangleIndex i j) := by
  fin_cases x <;> fin_cases y
  · exact (hxy rfl).elim
  · refine ⟨Equiv.ofBijective (![0,1,2,3,4,5,6,7] : Fin 8 → Fin 8) (by decide),0,1,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![0,2,1,3,4,5,6,7] : Fin 8 → Fin 8) (by decide),0,1,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![0,1,2,3,4,5,6,7] : Fin 8 → Fin 8) (by decide),0,3,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![0,1,2,4,3,5,6,7] : Fin 8 → Fin 8) (by decide),0,3,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![0,1,2,5,3,4,6,7] : Fin 8 → Fin 8) (by decide),0,3,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![0,1,2,3,4,5,6,7] : Fin 8 → Fin 8) (by decide),0,6,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![0,1,2,3,4,5,7,6] : Fin 8 → Fin 8) (by decide),0,6,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![1,0,2,3,4,5,6,7] : Fin 8 → Fin 8) (by decide),0,1,?_⟩
    decide
  · exact (hxy rfl).elim
  · refine ⟨Equiv.ofBijective (![1,2,0,3,4,5,6,7] : Fin 8 → Fin 8) (by decide),0,1,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![1,0,2,3,4,5,6,7] : Fin 8 → Fin 8) (by decide),0,3,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![1,0,2,4,3,5,6,7] : Fin 8 → Fin 8) (by decide),0,3,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![1,0,2,5,3,4,6,7] : Fin 8 → Fin 8) (by decide),0,3,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![1,0,2,3,4,5,6,7] : Fin 8 → Fin 8) (by decide),0,6,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![1,0,2,3,4,5,7,6] : Fin 8 → Fin 8) (by decide),0,6,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![2,0,1,3,4,5,6,7] : Fin 8 → Fin 8) (by decide),0,1,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![2,1,0,3,4,5,6,7] : Fin 8 → Fin 8) (by decide),0,1,?_⟩
    decide
  · exact (hxy rfl).elim
  · refine ⟨Equiv.ofBijective (![2,0,1,3,4,5,6,7] : Fin 8 → Fin 8) (by decide),0,3,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![2,0,1,4,3,5,6,7] : Fin 8 → Fin 8) (by decide),0,3,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![2,0,1,5,3,4,6,7] : Fin 8 → Fin 8) (by decide),0,3,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![2,0,1,3,4,5,6,7] : Fin 8 → Fin 8) (by decide),0,6,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![2,0,1,3,4,5,7,6] : Fin 8 → Fin 8) (by decide),0,6,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![3,4,5,0,1,2,6,7] : Fin 8 → Fin 8) (by decide),0,3,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![3,4,5,1,0,2,6,7] : Fin 8 → Fin 8) (by decide),0,3,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![3,4,5,2,0,1,6,7] : Fin 8 → Fin 8) (by decide),0,3,?_⟩
    decide
  · exact (hxy rfl).elim
  · refine ⟨Equiv.ofBijective (![3,4,5,0,1,2,6,7] : Fin 8 → Fin 8) (by decide),0,1,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![3,5,4,0,1,2,6,7] : Fin 8 → Fin 8) (by decide),0,1,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![3,4,5,0,1,2,6,7] : Fin 8 → Fin 8) (by decide),0,6,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![3,4,5,0,1,2,7,6] : Fin 8 → Fin 8) (by decide),0,6,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![4,3,5,0,1,2,6,7] : Fin 8 → Fin 8) (by decide),0,3,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![4,3,5,1,0,2,6,7] : Fin 8 → Fin 8) (by decide),0,3,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![4,3,5,2,0,1,6,7] : Fin 8 → Fin 8) (by decide),0,3,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![4,3,5,0,1,2,6,7] : Fin 8 → Fin 8) (by decide),0,1,?_⟩
    decide
  · exact (hxy rfl).elim
  · refine ⟨Equiv.ofBijective (![4,5,3,0,1,2,6,7] : Fin 8 → Fin 8) (by decide),0,1,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![4,3,5,0,1,2,6,7] : Fin 8 → Fin 8) (by decide),0,6,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![4,3,5,0,1,2,7,6] : Fin 8 → Fin 8) (by decide),0,6,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![5,3,4,0,1,2,6,7] : Fin 8 → Fin 8) (by decide),0,3,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![5,3,4,1,0,2,6,7] : Fin 8 → Fin 8) (by decide),0,3,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![5,3,4,2,0,1,6,7] : Fin 8 → Fin 8) (by decide),0,3,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![5,3,4,0,1,2,6,7] : Fin 8 → Fin 8) (by decide),0,1,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![5,4,3,0,1,2,6,7] : Fin 8 → Fin 8) (by decide),0,1,?_⟩
    decide
  · exact (hxy rfl).elim
  · refine ⟨Equiv.ofBijective (![5,3,4,0,1,2,6,7] : Fin 8 → Fin 8) (by decide),0,6,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![5,3,4,0,1,2,7,6] : Fin 8 → Fin 8) (by decide),0,6,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![0,1,2,3,4,5,6,7] : Fin 8 → Fin 8) (by decide),0,6,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![1,0,2,3,4,5,6,7] : Fin 8 → Fin 8) (by decide),0,6,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![2,0,1,3,4,5,6,7] : Fin 8 → Fin 8) (by decide),0,6,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![3,4,5,0,1,2,6,7] : Fin 8 → Fin 8) (by decide),0,6,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![4,3,5,0,1,2,6,7] : Fin 8 → Fin 8) (by decide),0,6,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![5,3,4,0,1,2,6,7] : Fin 8 → Fin 8) (by decide),0,6,?_⟩
    decide
  · exact (hxy rfl).elim
  · refine ⟨Equiv.ofBijective (![0,1,2,3,4,5,6,7] : Fin 8 → Fin 8) (by decide),6,7,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![0,1,2,3,4,5,7,6] : Fin 8 → Fin 8) (by decide),0,6,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![1,0,2,3,4,5,7,6] : Fin 8 → Fin 8) (by decide),0,6,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![2,0,1,3,4,5,7,6] : Fin 8 → Fin 8) (by decide),0,6,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![3,4,5,0,1,2,7,6] : Fin 8 → Fin 8) (by decide),0,6,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![4,3,5,0,1,2,7,6] : Fin 8 → Fin 8) (by decide),0,6,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![5,3,4,0,1,2,7,6] : Fin 8 → Fin 8) (by decide),0,6,?_⟩
    decide
  · refine ⟨Equiv.ofBijective (![0,1,2,3,4,5,7,6] : Fin 8 → Fin 8) (by decide),6,7,?_⟩
    decide
  · exact (hxy rfl).elim

#print axioms triangle_pair_normalization
end Blueprint.Thomson.Tail.Implementation
