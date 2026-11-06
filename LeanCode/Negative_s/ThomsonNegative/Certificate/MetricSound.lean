import ThomsonNegative.Certificate.FactorSound
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! An exact small Nat matrix-product gate certifies each floor metric inverse. -/
noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Certificate

theorem allBelow_sound (n : ℕ) (f : ℕ → Bool) :
    allBelow n f = true → ∀ i < n, f i = true := by
  induction n with
  | zero => intro _ i hi; omega
  | succ n ih =>
    intro h i hi
    change (allBelow n f && f n)=true at h
    simp only [Bool.and_eq_true] at h
    by_cases he : i=n
    · simpa only [he] using h.2
    · exact ih h.1 i (by omega)

theorem inverseEntryCheck_sound (n : ℕ) (F G : FactorData) (i j : ℕ)
    (h : inverseEntryCheck n F G i j=true) :
    ∑ k ∈ Finset.range n, F.eval i k * G.eval k j = if i=j then 1 else 0 := by
  let z := dotNat (fun k => factorEntry F i k) (fun k => factorEntry G k j) n
  have hz : z.1 = z.2 + (if i=j then 2^(F.bits+G.bits) else 0) := by
    simpa only [inverseEntryCheck,Bool.cond_eq_ite,Nat.beq_eq,beq_iff_eq,Nat.add_eq,Nat.pow_eq] using h
  have hr : pairReal z = if i=j then ((2:ℝ)^(F.bits+G.bits)) else 0 := by
    unfold pairReal
    rw [hz]
    split_ifs <;> push_cast <;> ring
  have hd : pairReal z / (2:ℝ)^(F.bits+G.bits) =
      ∑ k ∈ Finset.range n, F.eval i k * G.eval k j := by
    rw [dotNat_val,div_eq_mul_inv,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [FactorData.eval,pow_add]
    ring
  rw [← hd,hr]
  split_ifs <;> simp

def FactorData.matrix (n : ℕ) (F : FactorData) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => F.eval i.val j.val

theorem inverseCheck_sound (n : ℕ) (F G : FactorData)
    (h : inverseCheck n F G=true) : F.matrix n * G.matrix n = 1 := by
  ext i j
  have hi := allBelow_sound n _ h i.val i.isLt
  have hij := allBelow_sound n _ hi j.val j.isLt
  have hv := inverseEntryCheck_sound n F G i.val j.val hij
  simp only [Matrix.mul_apply,FactorData.matrix,Matrix.one_apply]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => F.eval i.val k * G.eval k j.val)]
  simpa only [Fin.val_inj] using hv

#print axioms inverseCheck_sound
end ThomsonNegative.Certificate
