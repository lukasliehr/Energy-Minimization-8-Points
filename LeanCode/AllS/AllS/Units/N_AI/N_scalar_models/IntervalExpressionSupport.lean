import AllS.Units.N_AI.N_data.IntervalExpressionGates
import AllS.Units.N_AI.N_scalar_models.ProductGateSupport

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def IntervalExpressionSupportStatement : Prop :=
  (∀ (q : ℚ), (QInterval.point q).asBox.Contains (q:ℝ)) ∧
  (∀ (I J : QInterval) (x y : ℝ), I.asBox.Contains x → J.asBox.Contains y →
    (I.add J).asBox.Contains (x+y)) ∧
  (∀ (I : QInterval) (x : ℝ), I.asBox.Contains x → I.neg.asBox.Contains (-x)) ∧
  (∀ (I : QInterval) (x : ℝ) (q : ℚ), I.asBox.Contains x →
    (I.scale q).asBox.Contains ((q:ℝ)*x)) ∧
  (∀ (I J : QInterval) (x y : ℝ), I.asBox.Contains x → J.asBox.Contains y →
    (I.mul J).asBox.Contains (x*y)) ∧
  (∀ (I : QInterval) (x : ℝ), I.asBox.Contains x → (0 < I.lo ∨ I.hi < 0) →
    I.inv.asBox.Contains (1/x))

theorem QInterval.point_contains (q : ℚ) : (QInterval.point q).asBox.Contains (q:ℝ) :=
  ⟨le_rfl,le_rfl⟩

theorem QInterval.add_contains {I J : QInterval} {x y : ℝ}
    (hx : I.asBox.Contains x) (hy : J.asBox.Contains y) :
    (I.add J).asBox.Contains (x+y) := Box.contains_add hx hy ⟨le_rfl,le_rfl⟩

theorem QInterval.neg_contains {I : QInterval} {x : ℝ}
    (hx : I.asBox.Contains x) : I.neg.asBox.Contains (-x) :=
  Box.contains_neg hx ⟨le_rfl,le_rfl⟩

theorem QInterval.scale_contains {I : QInterval} {x : ℝ} (q : ℚ)
    (hx : I.asBox.Contains x) : (I.scale q).asBox.Contains ((q:ℝ)*x) := by
  apply Box.contains_scale hx
  rcases le_total 0 q with hq | hq
  · exact Or.inl ⟨hq,min_le_left _ _,le_max_right _ _⟩
  · exact Or.inr ⟨hq,min_le_right _ _,le_max_left _ _⟩

theorem QInterval.mul_contains {I J : QInterval} {x y : ℝ}
    (hx : I.asBox.Contains x) (hy : J.asBox.Contains y) :
    (I.mul J).asBox.Contains (x*y) := by
  apply Box.contains_mul hx hy
  intro a ha b hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp [QInterval.asBox, QInterval.mul, min_le_iff, le_max_iff]

theorem QInterval.inv_contains {I : QInterval} {x : ℝ}
    (hx : I.asBox.Contains x) (hI : 0 < I.lo ∨ I.hi < 0) :
    I.inv.asBox.Contains (1/x) :=
  (Box.contains_inverse hx ⟨hI,le_rfl,le_rfl⟩).1

theorem QInterval.sum_contains {α : Type*} [Fintype α] (I : α → QInterval) (f : α → ℝ)
    (h : ∀ i, (I i).asBox.Contains (f i)) : (QInterval.sum I).asBox.Contains (∑ i, f i) := by
  constructor
  · change ((∑ i, (I i).lo:ℚ):ℝ) ≤ ∑ i, f i
    rw [Rat.cast_sum]
    exact Finset.sum_le_sum (fun i _ => (h i).1)
  · change (∑ i, f i) ≤ ((∑ i, (I i).hi:ℚ):ℝ)
    rw [Rat.cast_sum]
    exact Finset.sum_le_sum (fun i _ => (h i).2)

theorem QInterval.subset_contains {I J : QInterval} {x : ℝ}
    (hx : I.asBox.Contains x) (hg : I.SubsetGate J) : J.asBox.Contains x := by
  have hlo : (J.lo:ℝ) ≤ (I.lo:ℝ) := by exact_mod_cast hg.1
  have hhi : (I.hi:ℝ) ≤ (J.hi:ℝ) := by exact_mod_cast hg.2
  exact ⟨hlo.trans hx.1,hx.2.trans hhi⟩

theorem intervalExpressionSupport : IntervalExpressionSupportStatement :=
  ⟨QInterval.point_contains,fun _ _ _ _ => QInterval.add_contains,
    fun _ _ => QInterval.neg_contains,fun _ _ q => QInterval.scale_contains q,
    fun _ _ _ _ => QInterval.mul_contains,fun _ _ => QInterval.inv_contains⟩

#check intervalExpressionSupport
#print IntervalExpressionSupportStatement
#print axioms intervalExpressionSupport
#print axioms QInterval.sum_contains
#print axioms QInterval.subset_contains
end Blueprint.CAP
