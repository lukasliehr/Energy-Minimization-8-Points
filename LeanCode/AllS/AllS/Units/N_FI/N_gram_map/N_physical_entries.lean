import AllS.Units.N_FI.N_gram_map.N_linear_degree

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite
open MvPolynomial

set_option maxHeartbeats 0

def physicalSymmetricEntry {n : ℕ} (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  fun r c => (if r=i ∧ c=j then 1 else 0)+(if r=j ∧ c=i then 1 else 0)

def gramBlockPoly (a : ℝ) (d : ℕ) (p : MomentPivots d) (b : GramBlock d)
    (W : Matrix (Fin (gramBlockDimension d b)) (Fin (gramBlockDimension d b)) ℝ) : Poly3 :=
  ∑ i,∑ j,C (W i j)*gramKernel a d p b i j

def GramPhysicalEntryContract : Prop := ∀ a d p b,
  ∀ i j : Fin (gramBlockDimension d b),i<j →
    (physicalSymmetricEntry i j).IsSymm ∧
      gramBlockPoly a d p b (physicalSymmetricEntry i j)=C 2*gramKernel a d p b i j

theorem kernelQPoly_swap (k : ℕ) :
    rename (Equiv.swap (0 : Fin 3) 1) (kernelQPoly k)=kernelQPoly k := by
  induction k using Nat.twoStepInduction with
  | zero => simp [kernelQPoly]
  | one => simp only [kernelQPoly,map_sub,map_mul,rename_X,Equiv.swap_apply_left,Equiv.swap_apply_right,show Equiv.swap (0 : Fin 3) 1 2=2 by decide];ring
  | more k hk hk1 =>
    simp only [kernelQPoly,map_sub,map_mul,map_pow,rename_X,rename_C,map_one,hk,hk1]
    simp only [Equiv.swap_apply_left,Equiv.swap_apply_right,show Equiv.swap (0 : Fin 3) 1 2=2 by decide]
    ring

theorem kernelSPoly_transpose (k i j : ℕ) : kernelSPoly k i j=kernelSPoly k j i := by
  have h := reynolds_rename (MvPolynomial.X 0^i*MvPolynomial.X 1^j*kernelQPoly k)
    (Equiv.swap (0 : Fin 3) 1)
  have he : rename (Equiv.swap (0 : Fin 3) 1)
      (MvPolynomial.X 0^i*MvPolynomial.X 1^j*kernelQPoly k)=
      MvPolynomial.X 0^j*MvPolynomial.X 1^i*kernelQPoly k := by
    simp only [map_mul,map_pow,rename_X,kernelQPoly_swap]
    simp only [Equiv.swap_apply_left,Equiv.swap_apply_right,show Equiv.swap (0 : Fin 3) 1 2=2 by decide]
    ring
  rw [he] at h
  exact h.symm

theorem kernelRPoly_transpose (k i j : ℕ) : kernelRPoly k i j=kernelRPoly k j i := by
  simp only [kernelRPoly,kernelSPoly_transpose k i j]

theorem gramKernel_transpose (a : ℝ) (d : ℕ) (p : MomentPivots d) (b : GramBlock d)
    (i j : Fin (gramBlockDimension d b)) : gramKernel a d p b i j=gramKernel a d p b j i := by
  cases b with
  | inl k =>
    change momentBilinearKernel a d p k i j=momentBilinearKernel a d p k j i
    unfold momentBilinearKernel
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro c hc
    rw [kernelRPoly_transpose k.val c.val r.val]
    congr 1
    congr 1
    ring
  | inr b =>
    change scalarBilinearKernel b a d i j=scalarBilinearKernel b a d j i
    unfold scalarBilinearKernel
    congr 1
    ring

theorem physicalSymmetricEntry_isSymm {n : ℕ} (i j : Fin n) :
    (physicalSymmetricEntry i j).IsSymm := by
  ext r c
  simp only [Matrix.transpose_apply,physicalSymmetricEntry]
  simp only [and_comm]
  ring

theorem physicalEntry_sum {n : ℕ} (K : Fin n → Fin n → Poly3) (i j : Fin n) :
    (∑ r,∑ c,C (physicalSymmetricEntry i j r c)*K r c)=K i j+K j i := by
  have hgate (r c i j : Fin n) (f : Poly3) :
      C (if r=i ∧ c=j then (1 : ℝ) else 0)*f=if r=i ∧ c=j then f else 0 := by
    by_cases h : r=i ∧ c=j <;> simp [h]
  simp only [physicalSymmetricEntry,map_add,add_mul,Finset.sum_add_distrib]
  simp_rw [hgate,ite_and]
  simp

theorem gramBlockPoly_physical_entry (a : ℝ) (d : ℕ) (p : MomentPivots d) (b : GramBlock d)
    (i j : Fin (gramBlockDimension d b)) :
    gramBlockPoly a d p b (physicalSymmetricEntry i j)=C 2*gramKernel a d p b i j := by
  calc
    _ = gramKernel a d p b i j+gramKernel a d p b j i :=
      physicalEntry_sum (fun r c => gramKernel a d p b r c) i j
    _ = _ := by
      rw [gramKernel_transpose a d p b j i]
      simp only [map_ofNat]
      ring

theorem gram_map_physical_entries : GramPhysicalEntryContract := by
  intro a d p b i j hij
  exact ⟨physicalSymmetricEntry_isSymm i j,gramBlockPoly_physical_entry a d p b i j⟩

#check gram_map_physical_entries
#print axioms gram_map_physical_entries
end Blueprint.Thomson.Finite
