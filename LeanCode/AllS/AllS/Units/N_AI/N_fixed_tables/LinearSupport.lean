import AllS.Units.N_AI.N_fixed_tables.DenominatorSupport
import Mathlib.Data.Matrix.Mul

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP
set_option maxHeartbeats 0

def evalIntegerList (p : List ℤ) (a : ℝ) : ℝ :=
  (listPolynomial p).eval₂ (Int.castRingHom ℝ) a

theorem fixedTableClearedEntry (A p e d v q scale lam : ℝ)
    (he : e≠0) (hd : d≠0) (hlam : lam≠0)
    (hq : q=d*e*v) (hA : lam*A=scale*p*v) :
    A=scale*q*(p/e)/(lam*d) := by
  rw [hq]
  apply (eq_div_iff (mul_ne_zero hlam hd)).2
  field_simp
  nlinarith [hA]

theorem fixedTableRealRightInverse {n : ℕ}
    (A H C : Matrix (Fin n) (Fin n) ℝ) (q scale : ℝ)
    (d lam : Fin n → ℝ) (hq : q≠0) (hs : scale≠0)
    (hclear : ∀ i j,A i j=scale*q*C i j/(lam j*d j))
    (hprod : ∀ i j,∑ h,A i h*H h j=if i=j then scale*q else 0) :
    C * Matrix.of (fun i j => H i j/(lam i*d i))=1 := by
  ext i j
  apply (mul_left_cancel₀ (mul_ne_zero hs hq))
  change (scale*q)*(∑ h,C i h*(H h j/(lam h*d h)))=(scale*q)*(1:Matrix (Fin n) (Fin n) ℝ) i j
  rw [Finset.mul_sum]
  have he : (∑ h,scale*q*(C i h*(H h j/(lam h*d h))))=∑ h,A i h*H h j := by
    apply Finset.sum_congr rfl
    intro h hh
    rw [hclear]
    ring
  rw [he,hprod]
  by_cases hij : i=j <;> simp [hij,Matrix.one_apply]

theorem fixedTableRealRightInverse_apply {n : ℕ}
    (C D : Matrix (Fin n) (Fin n) ℝ) (h : C*D=1) (v : Fin n → ℝ) :
    C.mulVec (D.mulVec v)=v := by
  rw [Matrix.mulVec_mulVec,h,Matrix.one_mulVec]

#print axioms fixedTableClearedEntry
#print axioms fixedTableRealRightInverse
#print axioms fixedTableRealRightInverse_apply
end Blueprint.CAP
