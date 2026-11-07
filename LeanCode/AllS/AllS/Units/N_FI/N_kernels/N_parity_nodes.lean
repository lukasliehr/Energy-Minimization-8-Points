import AllS.Units.N_FI.N_kernels.N_named_features

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

/-- The source orders A,C,D,B and C,D,A,B. -/
def parityFiberLabel (odd : Bool) : Fin 4 → Fin 4 :=
  if odd then ![2,3,0,1] else ![0,2,3,1]
def parityFiberSize (odd : Bool) : Fin 4 → ℕ := if odd then oddFiberSizes else evenFiberSizes

/-- Pairs in lexicographic POINTS order, exactly as kernels.py filters them. -/
def parityFiberPairs (odd : Bool) : Fin 4 → List (Fin 4 × Fin 4) :=
  if odd then ![[(0,2),(0,3),(1,3)],[(0,2),(0,3),(1,2)],[(0,1),(2,3)],[(2,3)]]
  else ![[(0,1),(2,2),(2,3),(3,3)],[(0,2),(0,3),(1,3)],[(0,2),(0,3),(1,2)],[(0,0),(2,3)]]

def parityFiberZList (a : ℝ) (odd : Bool) (i : Fin 4) : List ℝ :=
  (parityFiberPairs odd i).map (fun p => contacts a p.1+contacts a p.2)
def parityFiberU (a : ℝ) (odd : Bool) (i : Fin 4) : ℝ := contacts a (parityFiberLabel odd i)
def parityLabelPoints (odd : Bool) : Finset (Fin 3 → Fin 4) :=
  (Finset.univ.biUnion contactLabelOrbit).filter (fun p => p 1 ≤ p 2 ∧ (odd = true → p 1 ≠ p 2))
def parityFiberLabelSet (odd : Bool) (i : Fin 4) : Finset (Fin 3 → Fin 4) :=
  ((parityFiberPairs odd i).map (fun p => ![parityFiberLabel odd i,p.1,p.2])).toFinset

def ParityNodesContract : Prop :=
  (∀ odd i, (parityFiberPairs odd i).length=parityFiberSize odd i) ∧
  (∀ odd, (Finset.univ.biUnion (parityFiberLabelSet odd))=parityLabelPoints odd) ∧
  (∀ odd i j, i≠j → Disjoint (parityFiberLabelSet odd i) (parityFiberLabelSet odd j)) ∧
  (∀ a : ℝ, physical a → ∀ odd,
    Function.Injective (parityFiberU a odd) ∧ ∀ i, (parityFiberZList a odd i).Nodup)

theorem parityFiberPairs_length : ∀ odd i,
    (parityFiberPairs odd i).length=parityFiberSize odd i := by decide

theorem parityFiberLabel_bijective : ∀ odd, Function.Bijective (parityFiberLabel odd) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem parityFiberLabelSet_union : ∀ odd,
    (Finset.univ.biUnion (parityFiberLabelSet odd))=parityLabelPoints odd := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem parityFiberLabelSet_disjoint : ∀ odd i j, i≠j →
    Disjoint (parityFiberLabelSet odd i) (parityFiberLabelSet odd j) := by decide

theorem parityFiberU_injective (a : ℝ) (ha : physical a) (odd : Bool) :
    Function.Injective (parityFiberU a odd) :=
  (contacts_injective a ha).comp (parityFiberLabel_bijective odd).1

theorem parity_fiber_cross_inequalities (a : ℝ) (ha : physical a) :
    contacts a 2+contacts a 3 < contacts a 0+contacts a 1 ∧
    contacts a 0+contacts a 3 < contacts a 1+contacts a 2 ∧
    contacts a 2+contacts a 3 < contacts a 0+contacts a 0 := by
  have hlo := (contact_order_packing_bounds a ha.1 ha.2).1.1
  have haa := ha.1
  have hau := ha.2
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hr := Real.sqrt_nonneg (2 : ℝ)
  have hr1 : 1 < Real.sqrt 2 := by nlinarith
  have hrne : Real.sqrt 2 ≠ 0 := by positivity
  have hinv : (Real.sqrt 2)⁻¹=Real.sqrt 2/2 := by
    field_simp [hrne]
    nlinarith
  have hp := mul_pos (show 0 < 1-a by linarith) (show 0 < Real.sqrt 2-1 by linarith)
  norm_num [contacts,div_eq_mul_inv,hinv]
  all_goals try dsimp
  constructor
  · linarith
  constructor
  · nlinarith
  · linarith

theorem parityFiberZList_nodup (a : ℝ) (ha : physical a) (odd : Bool) (i : Fin 4) :
    (parityFiberZList a odd i).Nodup := by
  obtain ⟨hD,hDB,hB,hC,hCA,hA,hsum,hsumneg⟩ := contact_order_ordered_contacts a ha
  obtain ⟨hcross0,hcross1,hcross2⟩ := parity_fiber_cross_inequalities a ha
  cases odd <;> fin_cases i <;> simp [parityFiberZList,parityFiberPairs]
  all_goals repeat' constructor
  all_goals intro he; linarith

theorem kernels_parity_nodes : ParityNodesContract := by
  refine ⟨parityFiberPairs_length,parityFiberLabelSet_union,parityFiberLabelSet_disjoint,?_⟩
  intro a ha odd
  exact ⟨parityFiberU_injective a ha odd,parityFiberZList_nodup a ha odd⟩

#check kernels_parity_nodes
#print axioms kernels_parity_nodes

#check ParityNodesContract
#print axioms ParityNodesContract
end Blueprint.Thomson.Finite
