import Lean_Code.FiniteCycles

noncomputable section
namespace SquareAntiprismVerification

def permutationOrbitSetoid {α : Type*} (e : Equiv.Perm α) : Setoid α where
  r := e.SameCycle
  iseqv := ⟨Equiv.Perm.SameCycle.refl e, fun h => h.symm, fun h g => h.trans g⟩

abbrev PermutationOrbit {α : Type*} (e : Equiv.Perm α) := Quotient (permutationOrbitSetoid e)

instance permutationOrbitFintype {α : Type*} [Finite α] (e : Equiv.Perm α) :
    Fintype (PermutationOrbit e) := Fintype.ofFinite _

def canonicalPermutationCycle {α : Type*} [Finite α] (e : Equiv.Perm α) (x : α) : PermutationCycle e :=
  Classical.choose (permutation_cycle_enumeration_exists e x)

lemma canonicalPermutationCycle_trace {α : Type*} [Finite α] (e : Equiv.Perm α) (x : α)
    (i : Fin ((canonicalPermutationCycle e x).size + 1)) :
    (canonicalPermutationCycle e x).point i = (⇑e)^[i.val] x :=
  Classical.choose_spec (permutation_cycle_enumeration_exists e x) i

lemma sameCycle_iterate {α : Type*} (e : Equiv.Perm α) (x : α) (n : ℕ) :
    e.SameCycle x ((⇑e)^[n] x) := by
  induction n with
  | zero => exact Equiv.Perm.SameCycle.refl e x
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ih.symm.apply_left.symm

lemma canonicalCycle_contains_iterate {α : Type*} [Finite α] (e : Equiv.Perm α) (x : α) (n : ℕ) :
    ∃ i, (canonicalPermutationCycle e x).point i = (⇑e)^[n] x := by
  induction n with
  | zero => exact ⟨0, canonicalPermutationCycle_trace e x 0⟩
  | succ n ih =>
    obtain ⟨i, hi⟩ := ih
    refine ⟨i + 1, ?_⟩
    rw [← (canonicalPermutationCycle e x).step, hi, Function.iterate_succ_apply']

theorem canonicalCycle_range_iff {α : Type*} [Fintype α] (e : Equiv.Perm α) (x y : α) :
    (∃ i, (canonicalPermutationCycle e x).point i = y) ↔ e.SameCycle x y := by
  classical
  constructor
  · rintro ⟨i, rfl⟩
    rw [canonicalPermutationCycle_trace]
    exact sameCycle_iterate e x i.val
  · intro h
    obtain ⟨n, _, _, hn⟩ := Equiv.Perm.SameCycle.exists_pow_eq e h
    rw [Equiv.Perm.coe_pow] at hn
    obtain ⟨i, hi⟩ := canonicalCycle_contains_iterate e x n
    exact ⟨i, hi.trans hn⟩

abbrev orbitPermutationCycle {α : Type*} [Finite α] (e : Equiv.Perm α) (q : PermutationOrbit e) :
    PermutationCycle e := canonicalPermutationCycle e q.out

lemma orbitPermutationCycle_class {α : Type*} [Finite α] (e : Equiv.Perm α) (q : PermutationOrbit e)
    (i : Fin ((orbitPermutationCycle e q).size + 1)) :
    (Quotient.mk (permutationOrbitSetoid e) ((orbitPermutationCycle e q).point i) : PermutationOrbit e) = q := by
  have h : e.SameCycle q.out ((orbitPermutationCycle e q).point i) := by
    change e.SameCycle q.out ((canonicalPermutationCycle e q.out).point i)
    rw [canonicalPermutationCycle_trace]
    exact sameCycle_iterate e q.out i.val
  exact (Quotient.sound h).symm.trans q.out_eq

def cyclePartitionMap {α : Type*} [Finite α] (e : Equiv.Perm α)
    (p : (q : PermutationOrbit e) × Fin ((orbitPermutationCycle e q).size + 1)) : α :=
  (orbitPermutationCycle e p.1).point p.2

theorem cyclePartitionMap_bijective {α : Type*} [Fintype α] (e : Equiv.Perm α) :
    Function.Bijective (cyclePartitionMap e) := by
  constructor
  · rintro ⟨q, i⟩ ⟨r, j⟩ heq
    have hq : q = r := by
      calc
        q = Quotient.mk (permutationOrbitSetoid e) ((orbitPermutationCycle e q).point i) :=
          (orbitPermutationCycle_class e q i).symm
        _ = Quotient.mk (permutationOrbitSetoid e) ((orbitPermutationCycle e r).point j) :=
          congrArg (Quotient.mk (permutationOrbitSetoid e)) heq
        _ = r := orbitPermutationCycle_class e r j
    subst r
    have hij : i = j := (orbitPermutationCycle e q).injective heq
    subst j
    rfl
  · intro y
    let q : PermutationOrbit e := Quotient.mk (permutationOrbitSetoid e) y
    have hsame : e.SameCycle q.out y := Quotient.exact q.out_eq
    obtain ⟨i, hi⟩ := (canonicalCycle_range_iff e q.out y).mpr hsame
    exact ⟨⟨q, i⟩, hi⟩

/-- The canonical cycles partition every element exactly once. -/
def cyclePartitionEquiv {α : Type*} [Fintype α] (e : Equiv.Perm α) :
    ((q : PermutationOrbit e) × Fin ((orbitPermutationCycle e q).size + 1)) ≃ α :=
  Equiv.ofBijective (cyclePartitionMap e) (cyclePartitionMap_bijective e)

theorem sum_over_permutation_cycles {α M : Type*} [Fintype α] [AddCommMonoid M]
    (e : Equiv.Perm α) (f : α → M) :
    ∑ q : PermutationOrbit e, ∑ i, f ((orbitPermutationCycle e q).point i) = ∑ x, f x := by
  classical
  have h := Equiv.sum_comp (cyclePartitionEquiv e) f
  change (∑ p : (q : PermutationOrbit e) × Fin ((orbitPermutationCycle e q).size + 1),
    f ((orbitPermutationCycle e p.1).point p.2)) = ∑ x, f x at h
  simpa only [Fintype.sum_sigma] using h

theorem sum_permutation_cycle_lengths {α : Type*} [Fintype α] (e : Equiv.Perm α) :
    ∑ q : PermutationOrbit e, ((orbitPermutationCycle e q).size + 1) = Fintype.card α := by
  have h := sum_over_permutation_cycles e (fun _ => (1 : ℕ))
  simpa using h

end SquareAntiprismVerification
