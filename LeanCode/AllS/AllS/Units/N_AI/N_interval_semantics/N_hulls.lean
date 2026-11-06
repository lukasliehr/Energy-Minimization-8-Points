import AllS.Units.N_AI.N_interval_semantics.N_affine
import AllS.Units.N_AI.N_interval_semantics.N_inverse_sqrt
import Blueprint.Target

namespace Blueprint.CAP
namespace Box
def WidenGate (I K : Box) : Prop := K.lo ≤ I.lo ∧ I.hi ≤ K.hi
def intersection (I J : Box) : Box := ⟨max I.lo J.lo, min I.hi J.hi⟩
end Box
def IntervalHullsStatement : Prop :=
  (∀ {I K : Box} {x : ℝ}, I.Contains x → Box.WidenGate I K → K.Contains x) ∧
  (∀ {I J : Box} {x : ℝ}, I.Contains x → J.Contains x →
    (Box.intersection I J).Contains x ∧ (Box.intersection I J).WellFormed) ∧
  (∀ (f : ℝ → ℝ) (μ : ℝ), 0<μ → (∀ x∈cellDomain, μ≤|f x|) →
    ∀ x∈cellDomain, f x≠0)
theorem Box.contains_widen {I K : Box} {x : ℝ}
    (hx : I.Contains x) (hg : I.WidenGate K) : K.Contains x := by
  have hl : (K.lo:ℝ)≤I.lo := by exact_mod_cast hg.1
  have hu : (I.hi:ℝ)≤K.hi := by exact_mod_cast hg.2
  exact ⟨hl.trans hx.1, hx.2.trans hu⟩

theorem Box.contains_intersection {I J : Box} {x : ℝ}
    (hx : I.Contains x) (hy : J.Contains x) :
    (I.intersection J).Contains x ∧ (I.intersection J).WellFormed := by
  have hlo : max (I.lo:ℝ) J.lo ≤ x := max_le hx.1 hy.1
  have hhi : x ≤ min (I.hi:ℝ) J.hi := le_min hx.2 hy.2
  constructor
  · simpa [Contains, intersection] using And.intro hlo hhi
  · have hr := hlo.trans hhi
    exact_mod_cast hr

theorem nonzero_of_uniform_separation (f : ℝ→ℝ) (μ : ℝ) (hμ : 0<μ)
    (hsep : ∀ x∈cellDomain, μ≤|f x|) : ∀ x∈cellDomain, f x≠0 := by
  intro x hx hz
  have h := hsep x hx
  rw [hz, abs_zero] at h
  exact (not_le_of_gt hμ) h

theorem interval_semantics_hulls : IntervalHullsStatement :=
  ⟨Box.contains_widen, Box.contains_intersection, nonzero_of_uniform_separation⟩
#check interval_semantics_hulls
#print interval_semantics_hulls
#print axioms interval_semantics_hulls
end Blueprint.CAP
