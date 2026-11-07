import AllS.Units.N_FI.N_raw_projection.N_power_recurrences
import AllS.Units.N_FI.N_kernels.N_named_features
import Mathlib.GroupTheory.Perm.Fin

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

set_option maxHeartbeats 0

def rawCyclicPower (n k : ℕ) : Poly3 :=
  MvPolynomial.X 0^n*(MvPolynomial.X 1*MvPolynomial.X 2)^k+
  MvPolynomial.X 1^n*(MvPolynomial.X 0*MvPolynomial.X 2)^k+
  MvPolynomial.X 2^n*(MvPolynomial.X 0*MvPolynomial.X 1)^k

def rawParityCyclic (i j k : ℕ) : Poly3 :=
  MvPolynomial.C (1/3 : ℝ)*
    (MvPolynomial.X 0^i*(MvPolynomial.X 1+MvPolynomial.X 2)^j*(MvPolynomial.X 1*MvPolynomial.X 2)^k+
     MvPolynomial.X 1^i*(MvPolynomial.X 0+MvPolynomial.X 2)^j*(MvPolynomial.X 0*MvPolynomial.X 2)^k+
     MvPolynomial.X 2^i*(MvPolynomial.X 0+MvPolynomial.X 1)^j*(MvPolynomial.X 0*MvPolynomial.X 1)^k)

def rawParityInvariant (i j k : ℕ) : Poly3 :=
  MvPolynomial.C (1/3 : ℝ)*∑ l ∈ Finset.range (j+1),
    (-1:Poly3)^l*(j.choose l:Poly3)*sigma^(j-l)*
      (if k ≤ i + l then e3^k*rawPowerSum (i+l-k)
       else e3^(i+l)*rawPairPowerSum (k-(i+l)))

theorem rawCyclicPower_formula (n k : ℕ) :
    rawCyclicPower n k=if k≤n then e3^k*rawPowerSum (n-k)
      else e3^n*rawPairPowerSum (k-n) := by
  split_ifs with h
  · obtain ⟨m,rfl⟩ : ∃ m,n=k+m := ⟨n-k,by omega⟩
    simp only [rawCyclicPower,rawPowerSum,e3,Nat.add_sub_cancel_left,pow_add,mul_pow]
    ring
  · obtain ⟨m,rfl⟩ : ∃ m,k=n+m := ⟨k-n,by omega⟩
    simp only [rawCyclicPower,rawPairPowerSum,e3,Nat.add_sub_cancel_left,pow_add,mul_pow]
    ring

private theorem rawParity_binomial {R : Type*} [CommRing R] (u v w : R) (i j k : ℕ) :
    u^i*(v+w)^j*(v*w)^k=
      ∑ l ∈ Finset.range (j+1),(-1:R)^l*(j.choose l:R)*(u+v+w)^(j-l)*
        (u^(i+l)*(v*w)^k) := by
  rw [show v+w=(-u)+(u+v+w) by ring,add_pow,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l hl
  rw [show -u=(-1:R)*u by ring,mul_pow,pow_add]
  ring

theorem rawParityCyclic_formula (i j k : ℕ) : rawParityCyclic i j k=rawParityInvariant i j k := by
  unfold rawParityCyclic rawParityInvariant
  congr 1
  rw [rawParity_binomial,rawParity_binomial,rawParity_binomial,
    ← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  rw [← rawCyclicPower_formula]
  simp only [rawCyclicPower,sigma]
  ring

theorem reynolds_parity_cyclic (i j k : ℕ) :
    reynolds (parityMonomial (i,j,k))=rawParityCyclic i j k := by
  have hp : (Finset.univ : Finset (Equiv.Perm (Fin 3)))=
      {Equiv.refl _,Equiv.swap 0 1,Equiv.swap 0 2,Equiv.swap 1 2,
        (Equiv.swap 0 1).trans (Equiv.swap 1 2),(Equiv.swap 1 2).trans (Equiv.swap 0 1)} := by
    decide
  apply MvPolynomial.funext
  intro x
  norm_num [reynolds,parityMonomial,parityZ,parityW,rawParityCyclic,hp,
    Finset.sum_insert,Equiv.swap_apply_def,Equiv.trans_apply]
  rw [Finset.sum_insert (by decide),Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),Finset.sum_singleton]
  norm_num [Equiv.swap_apply_def,Equiv.trans_apply,Fin.ext_iff]
  ring

def RawParityFormulaContract : Prop := ∀ i j k : ℕ,
  reynolds (parityMonomial (i,j,k))=rawParityInvariant i j k

theorem raw_projection_parity_formula : RawParityFormulaContract := by
  intro i j k
  rw [reynolds_parity_cyclic,rawParityCyclic_formula]

#print axioms raw_projection_parity_formula
end Blueprint.Thomson.Finite
