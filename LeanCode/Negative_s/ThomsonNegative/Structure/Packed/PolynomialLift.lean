import ThomsonNegative.Structure.Packed.ListPoly
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Lifting radix identities to polynomial identities (workstream F4; paper Corollary `cor:packed-fixed-table`)

Coefficient lists over `ℤ` (lowest first; `Packed.ListPoly`). `l1 P = Σ |Pₖ|` is submultiplicative under
`convL`; `kronecker`: if `2 · l1 P < B` and `P(B) = 0` then `P` vanishes identically (balanced digits are
unique). `sumL` sums a list of polynomials.
-/

namespace ThomsonNegative.Structure.PolynomialLift

open ThomsonNegative.Structure.Packed

/-- `Σ |Pₖ|`. -/
def l1 (P : List ℤ) : ℕ := (P.map Int.natAbs).sum

@[simp] theorem l1_nil : l1 [] = 0 := rfl
theorem l1_cons (c : ℤ) (P : List ℤ) : l1 (c :: P) = c.natAbs + l1 P := by simp [l1]

theorem l1_addL : ∀ P Q : List ℤ, l1 (addL P Q) ≤ l1 P + l1 Q
  | [], Q => by simp [addL]
  | c :: P, [] => by simp [addL]
  | c :: P, d :: Q => by
    simp only [addL, l1_cons]
    have := l1_addL P Q
    have := Int.natAbs_add_le c d
    omega

theorem l1_scaleL (x : ℤ) : ∀ P : List ℤ, l1 (scaleL x P) = x.natAbs * l1 P
  | [] => by simp [scaleL]
  | c :: P => by simp only [scaleL, l1_cons, l1_scaleL x P, Int.natAbs_mul]; ring

theorem l1_convL : ∀ P Q : List ℤ, l1 (convL P Q) ≤ l1 P * l1 Q
  | [], Q => by simp [convL]
  | c :: P, Q => by
    simp only [convL, l1_cons]
    have h1 := l1_addL (scaleL c Q) (0 :: convL P Q)
    have h2 := l1_convL P Q
    rw [l1_scaleL, l1_cons] at h1
    simp only [Int.natAbs_zero, zero_add] at h1
    nlinarith

/-- Sum of a list of polynomials. -/
def sumL : List (List ℤ) → List ℤ
  | [] => []
  | P :: Ps => addL P (sumL Ps)

theorem horner_sumL {R : Type*} [CommRing R] (f : ℤ →+* R) (t : R) : ∀ Ps : List (List ℤ),
    horner t ((sumL Ps).map f) = (Ps.map fun P => horner t (P.map f)).sum
  | [] => by simp [sumL]
  | P :: Ps => by simp [sumL, map_addL, horner_addL, horner_sumL f t Ps]

theorem l1_sumL : ∀ Ps : List (List ℤ), l1 (sumL Ps) ≤ (Ps.map l1).sum
  | [] => by simp [sumL]
  | P :: Ps => by
    simp only [sumL, List.map_cons, List.sum_cons]
    have := l1_addL P (sumL Ps)
    have := l1_sumL Ps
    omega

theorem natAbs_le_l1 : ∀ (P : List ℤ) (c : ℤ), c ∈ P → c.natAbs ≤ l1 P
  | [], c, h => by simp at h
  | d :: P, c, h => by
    rw [l1_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := natAbs_le_l1 P c h; omega

/-- **Kronecker injectivity**: small coefficients and `P(B) = 0` force `P = 0` coefficientwise. -/
theorem kronecker (B : ℕ) (hB : 2 ≤ B) : ∀ P : List ℤ, 2 * l1 P < B → horner (B : ℤ) P = 0 → ∀ c ∈ P, c = 0
  | [], _, _, c, h => by simp at h
  | d :: P, hl, h0, c, hc => by
    rw [l1_cons] at hl
    rw [horner_cons] at h0
    have hd : d = -(B : ℤ) * horner (B : ℤ) P := by linarith
    have hdB : d.natAbs < B := by omega
    have hd0 : d = 0 := by
      by_contra hne
      have hP : horner (B : ℤ) P ≠ 0 := by
        intro hz; rw [hz, mul_zero] at hd; exact hne hd
      have : (B : ℤ) ≤ |d| := by
        rw [hd, abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℤ) ≤ B)]
        have : (1 : ℤ) ≤ |horner (B : ℤ) P| := Int.one_le_abs hP
        nlinarith
      have : (d.natAbs : ℤ) = |d| := Int.natCast_natAbs d
      omega
    have hP0 : horner (B : ℤ) P = 0 := by
      rw [hd0] at hd
      have hBz : (B : ℤ) ≠ 0 := by exact_mod_cast (by omega : B ≠ 0)
      rcases mul_eq_zero.mp hd.symm with h | h
      · exact absurd (neg_eq_zero.mp h) hBz
      · exact h
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hd0
    · exact kronecker B hB P (by omega) hP0 c hc

theorem evalZ_eq_zero_of_coeffs : ∀ (P : List ℤ), (∀ c ∈ P, c = 0) → ∀ t : ℝ, evalZ P t = 0
  | [], _, t => by simp [evalZ]
  | d :: P, h, t => by
    have hd := h d (by simp)
    have := evalZ_eq_zero_of_coeffs P (fun c hc => h c (by simp [hc])) t
    simp only [evalZ, List.map_cons, horner_cons] at this ⊢
    rw [this, hd]; simp

/-- **Lifting**: a polynomial with small coefficients vanishing at the radix vanishes identically. -/
theorem lift (B : ℕ) (hB : 2 ≤ B) (P : List ℤ) (hl : 2 * l1 P < B) (h0 : horner (B : ℤ) P = 0) (t : ℝ) :
    evalZ P t = 0 :=
  evalZ_eq_zero_of_coeffs P (kronecker B hB P hl h0) t

theorem evalZ_addL (P Q : List ℤ) (t : ℝ) : evalZ (addL P Q) t = evalZ P t + evalZ Q t := by
  simp only [evalZ]
  rw [show (Int.cast : ℤ → ℝ) = (Int.castRingHom ℝ : ℤ → ℝ) from rfl, map_addL, horner_addL]

theorem evalZ_scaleL (x : ℤ) (P : List ℤ) (t : ℝ) : evalZ (scaleL x P) t = x * evalZ P t := by
  simp only [evalZ]
  rw [show (Int.cast : ℤ → ℝ) = (Int.castRingHom ℝ : ℤ → ℝ) from rfl, map_scaleL, horner_scaleL]

theorem evalZ_sumL (Ps : List (List ℤ)) (t : ℝ) : evalZ (sumL Ps) t = (Ps.map fun P => evalZ P t).sum := by
  simp only [evalZ]
  rw [show (Int.cast : ℤ → ℝ) = (Int.castRingHom ℝ : ℤ → ℝ) from rfl, horner_sumL]

theorem hornerZ_addL (B : ℤ) (P Q : List ℤ) : horner B (addL P Q) = horner B P + horner B Q := horner_addL B P Q
theorem hornerZ_scaleL (B x : ℤ) (P : List ℤ) : horner B (scaleL x P) = x * horner B P := horner_scaleL B x P
theorem hornerZ_convL (B : ℤ) (P Q : List ℤ) : horner B (convL P Q) = horner B P * horner B Q := horner_convL B P Q
theorem hornerZ_sumL (B : ℤ) (Ps : List (List ℤ)) : horner B (sumL Ps) = (Ps.map fun P => horner B P).sum := by
  have h := horner_sumL (RingHom.id ℤ) B Ps
  simpa using h

#print axioms lift

end ThomsonNegative.Structure.PolynomialLift
