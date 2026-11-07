import AllS.Units.N_G.N_stationary_flow
import Lean_Code.FiniteCycles

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Tail.Implementation

/-- A simple directed cycle on the actual eight vertices. -/
structure FlowCycle where
  size : ℕ
  length_ge : 3 ≤ size+1
  point : Fin (size+1) → Fin 8
  injective : Function.Injective point

def FlowCycle.Positive (C : FlowCycle) (f : Fin 8 → Fin 8 → ℝ) : Prop :=
  ∀ i, 0 < f (C.point i) (C.point (i+1))

theorem FlowCycle.length_le (C : FlowCycle) : C.size+1 ≤ 8 := by
  simpa using Fintype.card_le_of_injective C.point C.injective

theorem circulation_outgoing (f : Fin 8 → Fin 8 → ℝ) (hf : NonnegativeCirculation f)
    (i j : Fin 8) (hij : 0 < f i j) : ∃ k, 0 < f j k := by
  have hs : 0 < ∑ k : Fin 8, f k j := hij.trans_le
    (Finset.single_le_sum (fun k hk => hf.1 k j) (Finset.mem_univ i))
  rw [← hf.2.2.2 j] at hs
  by_contra hn
  push_neg at hn
  exact (not_lt_of_ge (Finset.sum_nonpos (fun k hk => hn k))) hs

/-- Pigeonhole repetition followed by the existing minimal-period API gives
an injective cyclic enumeration for a finite functional orbit. -/
theorem finite_orbit_cycle (g : Fin 8 → Fin 8) (a : Fin 8) :
    ∃ (n : ℕ) (v : Fin (n+1) → Fin 8), Function.Injective v ∧
      (∀ i, g (v i)=v (i+1)) ∧ (∀ i, ∃ k, v i=g^[k] a) := by
  obtain ⟨i,j,hij,he⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin 9 => g^[i.val] a) (by norm_num)
  have hrep : ∃ r q : ℕ, r < q ∧ g^[r] a=g^[q] a := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i.val,j.val,h,he⟩
    · exact ⟨j.val,i.val,h,he.symm⟩
  obtain ⟨r,q,hrq,heq⟩ := hrep
  let x := g^[r] a
  have hp : Function.IsPeriodicPt g (q-r) x := by
    change g^[q-r] (g^[r] a)=g^[r] a
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hrq.le]
    exact heq.symm
  have hpos := hp.minimalPeriod_pos (by omega)
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  let v : Fin (n+1) → Fin 8 := fun i => g^[i.val] x
  have hv : Function.Injective v := by
    intro i j hij
    apply Fin.ext
    apply Function.iterate_injOn_Iio_minimalPeriod (f := g) (x := x)
    · simpa only [Set.mem_Iio,hn] using i.isLt
    · simpa only [Set.mem_Iio,hn] using j.isLt
    · exact hij
  have hstep (i : Fin (n+1)) : g (v i)=v (i+1) := by
    by_cases hi : i=Fin.last n
    · subst i
      have hh := Function.isPeriodicPt_minimalPeriod g x
      rw [hn] at hh
      rw [Fin.last_add_one]
      change g (g^[n] x)=x
      change g^[n+1] x=x at hh
      simpa only [Function.iterate_succ_apply'] using hh
    · change g (g^[i.val] x)=g^[(i+1).val] x
      rw [Fin.val_add_one,if_neg hi,Function.iterate_succ_apply']
  refine ⟨n,v,hv,hstep,?_⟩
  intro i
  exact ⟨i.val+r,(Function.iterate_add_apply g i.val r a).symm⟩

theorem cycle_decomposition_find_cycle (f : Fin 8 → Fin 8 → ℝ)
    (hf : NonnegativeCirculation f) (hnonzero : ∃ i j, 0 < f i j) :
    ∃ C : FlowCycle, C.Positive f := by
  classical
  let g : Fin 8 → Fin 8 := fun i =>
    if h : ∃ j, 0 < f i j then h.choose else i
  have hg (i : Fin 8) (hi : ∃ j, 0 < f i j) : 0 < f i (g i) := by
    dsimp [g]
    rw [dif_pos hi]
    exact hi.choose_spec
  obtain ⟨a,b,hab⟩ := hnonzero
  have hactive (k : ℕ) : ∃ j, 0 < f (g^[k] a) j := by
    induction k with
    | zero => exact ⟨b,hab⟩
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact circulation_outgoing f hf _ _ (hg _ ih)
  obtain ⟨n,v,hv,hstep,horbit⟩ := finite_orbit_cycle g a
  have hpositive (i : Fin (n+1)) : 0 < f (v i) (v (i+1)) := by
    rw [← hstep i]
    obtain ⟨k,hk⟩ := horbit i
    rw [hk]
    exact hg _ (hactive k)
  have hlength : 3 ≤ n+1 := by
    by_contra hn
    have hsmall : n=0 ∨ n=1 := by omega
    rcases hsmall with rfl | rfl
    · have h := hpositive 0
      have he : (0+1 : Fin 1)=0 := by decide
      rw [he,hf.2.1] at h
      exact (lt_irrefl 0) h
    · apply hf.2.2.1 (v 0) (v 1)
      constructor
      · simpa using hpositive 0
      · simpa using hpositive 1
  exact ⟨⟨n,hlength,v,hv⟩,hpositive⟩

#check cycle_decomposition_find_cycle
#print axioms cycle_decomposition_find_cycle
end Blueprint.Thomson.Tail.Implementation
