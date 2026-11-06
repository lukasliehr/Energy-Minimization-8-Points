import AllS.Units.N_GI.N_cube_k4_noE.N_four_cycle_false

set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

/-- The six unordered pairs on four explicitly indexed vertices. -/
def fourGraphAdj (b : Fin 6 → Bool) (i j : Fin 4) : Prop :=
  ((i=0 ∧ j=1) ∨ (i=1 ∧ j=0)) ∧ b 0=true ∨
  ((i=0 ∧ j=2) ∨ (i=2 ∧ j=0)) ∧ b 1=true ∨
  ((i=0 ∧ j=3) ∨ (i=3 ∧ j=0)) ∧ b 2=true ∨
  ((i=1 ∧ j=2) ∨ (i=2 ∧ j=1)) ∧ b 3=true ∨
  ((i=1 ∧ j=3) ∨ (i=3 ∧ j=1)) ∧ b 4=true ∨
  ((i=2 ∧ j=3) ∨ (i=3 ∧ j=2)) ∧ b 5=true

instance (b : Fin 6 → Bool) (i j : Fin 4) : Decidable (fourGraphAdj b i j) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _))

/-- Respectively three-vertex path, four-vertex path, triangle, four-cycle. -/
def fourPatternBits (p : Fin 4) : Fin 6 → Bool :=
  match p.val with
  | 0 => ![true,false,false,true,false,false]
  | 1 => ![true,false,false,true,false,true]
  | 2 => ![true,true,false,true,false,false]
  | _ => ![true,false,true,true,false,true]

abbrev fourGraphDegree (b : Fin 6 → Bool) (i : Fin 4) : ℕ :=
  (Finset.univ.filter (fourGraphAdj b i)).card

/-- This is a finite kernel decision over64 graphs and24 permutations. -/
theorem fourGraph_classification : ∀ b : Fin 6 → Bool,
    (∀ i : Fin 4,fourGraphDegree b i≤2) →
    (∃ i : Fin 4,fourGraphDegree b i=2) →
    ∃ p : Fin 4,∃ e : Equiv.Perm (Fin 4),∀ i j,
      fourGraphAdj b (e i) (e j) ↔ fourGraphAdj (fourPatternBits p) i j := by
  decide +kernel

#print axioms fourGraph_classification
end Blueprint.Thomson.Tail.Implementation
