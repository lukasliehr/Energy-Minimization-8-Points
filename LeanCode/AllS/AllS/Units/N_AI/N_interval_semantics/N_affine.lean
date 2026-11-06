import Blueprint.CAPContracts
import Blueprint.Target

namespace Blueprint.CAP
namespace Box
def NegGate (I K : Box) : Prop := K.lo ≤ -I.hi ∧ -I.lo ≤ K.hi
def ScaleGate (q : ℚ) (I K : Box) : Prop :=
  (0 ≤ q ∧ K.lo ≤ q * I.lo ∧ q * I.hi ≤ K.hi) ∨
  (q ≤ 0 ∧ K.lo ≤ q * I.hi ∧ q * I.lo ≤ K.hi)
end Box

def IntervalAffineStatement : Prop :=
  (∀ {I J K : Box} {x y : ℝ}, I.Contains x → J.Contains y →
    Box.AddGate I J K → K.Contains (x+y)) ∧
  (∀ {I K : Box} {x : ℝ}, I.Contains x → Box.NegGate I K → K.Contains (-x)) ∧
  (∀ {I K : Box} {x : ℝ} {q : ℚ}, I.Contains x →
    Box.ScaleGate q I K → K.Contains ((q : ℝ)*x))

theorem Box.contains_neg {I K : Box} {x : ℝ}
    (hx : I.Contains x) (hg : I.NegGate K) : K.Contains (-x) := by
  have h₁ : (K.lo : ℝ) ≤ -(I.hi : ℝ) := by exact_mod_cast hg.1
  have h₂ : -(I.lo : ℝ) ≤ (K.hi : ℝ) := by exact_mod_cast hg.2
  exact ⟨h₁.trans (neg_le_neg hx.2), (neg_le_neg hx.1).trans h₂⟩

theorem Box.contains_scale {I K : Box} {x : ℝ} {q : ℚ}
    (hx : I.Contains x) (hg : ScaleGate q I K) : K.Contains ((q : ℝ)*x) := by
  rcases hg with ⟨hq, hl, hu⟩ | ⟨hq, hl, hu⟩
  · have hqR : (0 : ℝ) ≤ q := by exact_mod_cast hq
    have hlR : (K.lo : ℝ) ≤ (q : ℝ) * I.lo := by exact_mod_cast hl
    have huR : (q : ℝ) * I.hi ≤ (K.hi : ℝ) := by exact_mod_cast hu
    exact ⟨hlR.trans (mul_le_mul_of_nonneg_left hx.1 hqR),
      (mul_le_mul_of_nonneg_left hx.2 hqR).trans huR⟩
  · have hqR : (q : ℝ) ≤ 0 := by exact_mod_cast hq
    have hlR : (K.lo : ℝ) ≤ (q : ℝ) * I.hi := by exact_mod_cast hl
    have huR : (q : ℝ) * I.lo ≤ (K.hi : ℝ) := by exact_mod_cast hu
    exact ⟨hlR.trans (mul_le_mul_of_nonpos_left hx.2 hqR),
      (mul_le_mul_of_nonpos_left hx.1 hqR).trans huR⟩

theorem interval_semantics_affine : IntervalAffineStatement :=
  ⟨Box.contains_add, Box.contains_neg, Box.contains_scale⟩
#check interval_semantics_affine
#print interval_semantics_affine
#print axioms interval_semantics_affine
end Blueprint.CAP
