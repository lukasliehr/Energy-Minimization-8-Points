import Lean_Code.CircleOrder

noncomputable section
namespace SquareAntiprismVerification

lemma permutation_minimalPeriod_pos {α : Type*} [Finite α] (e : Equiv.Perm α) (x : α) :
    0 < Function.minimalPeriod e x := by
  apply Function.IsPeriodicPt.minimalPeriod_pos (orderOf_pos e)
  change (⇑e)^[orderOf e] x = x
  rw [← Equiv.Perm.coe_pow, pow_orderOf_eq_one]
  rfl

/-- One full directed cycle of a finite permutation. Injectivity here is
of the permutation's elements, not of any projected graph vertices. -/
structure PermutationCycle {α : Type*} (e : Equiv.Perm α) where
  size : ℕ
  point : Fin (size + 1) → α
  injective : Function.Injective point
  step : ∀ i, e (point i) = point (i + 1)

theorem permutation_cycle_enumeration_exists {α : Type*} [Finite α] (e : Equiv.Perm α) (x : α) :
    ∃ C : PermutationCycle e, ∀ i, C.point i = (⇑e)^[i.val] x := by
  have hnpos := permutation_minimalPeriod_pos e x
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
  let point : Fin (n + 1) → α := fun i => (⇑e)^[i.val] x
  have hinj : Function.Injective point := by
    intro i j hij
    apply Fin.ext
    apply Function.iterate_injOn_Iio_minimalPeriod (f := e) (x := x)
    · simpa only [Set.mem_Iio, hn] using i.isLt
    · simpa only [Set.mem_Iio, hn] using j.isLt
    · exact hij
  have hstep (i : Fin (n + 1)) : e (point i) = point (i + 1) := by
    by_cases hi : i = Fin.last n
    · subst i
      have hp := Function.isPeriodicPt_minimalPeriod e x
      rw [hn] at hp
      rw [Fin.last_add_one]
      change e ((⇑e)^[n] x) = x
      change (⇑e)^[n + 1] x = x at hp
      simpa only [Function.iterate_succ_apply'] using hp
    · change e ((⇑e)^[i.val] x) = (⇑e)^[(i + 1).val] x
      rw [Fin.val_add_one, if_neg hi, Function.iterate_succ_apply']
  exact ⟨⟨n, point, hinj, hstep⟩, fun _ => rfl⟩

theorem permutation_cycle_exists {α : Type*} [Finite α] (e : Equiv.Perm α) (x : α) :
    ∃ C : PermutationCycle e, C.point 0 = x := by
  obtain ⟨C, hC⟩ := permutation_cycle_enumeration_exists e x
  exact ⟨C, hC 0⟩

namespace PermutationCycle

variable {α : Type*} {e : Equiv.Perm α}

lemma length_le_card [Fintype α] (C : PermutationCycle e) : C.size + 1 ≤ Fintype.card α := by
  simpa using Fintype.card_le_of_injective C.point C.injective

end PermutationCycle

end SquareAntiprismVerification
