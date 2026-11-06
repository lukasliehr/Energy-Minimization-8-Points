import AllS.Units.N_FI.N_moment_kernels.N_canonical_QSR
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Units.N_FI.N_moment_kernels.N_pivot_nonzero
import AllS.Units.N_FI.N_moment_kernels.N_nullspace_columns

noncomputable section
namespace Blueprint.Thomson.Finite

/-- The actual candidate nullspace for any of the eleven source pivot keys. -/
def CandidateMomentKernelContract : Prop := ∀ a,physical a → ∀ m k : ℕ,k≤8 →
  ∀ p : Fin m,(∃ j : Fin 11,momentPivotKey j=(k,p.val)) →
    (∀ f g : MomentFreeIndex p,
      momentNullspaceColumn (fun i => momentP k i.val a) p f.val g=(if f=g then 1 else 0)) ∧
    canonicalMoment m k (X a)*momentNullspaceColumn (fun i => momentP k i.val a) p=0 ∧
    (∀ v : Fin m → ℝ,(canonicalMoment m k (X a)).mulVec v=0 ↔
      ∃ w : MomentFreeIndex p → ℝ,(momentNullspaceColumn (fun i => momentP k i.val a) p).mulVec w=v) ∧
    Function.Injective (fun w : MomentFreeIndex p → ℝ =>
      (momentNullspaceColumn (fun i => momentP k i.val a) p).mulVec w)

theorem candidate_moment_nullspace : CandidateMomentKernelContract := by
  intro a ha m k hk p hp
  obtain ⟨j,hj⟩ := hp
  have hP : momentP k p.val a≠0 := by
    have h := (moment_kernels_pivot_nonzero a ha j).2
    simpa only [show (momentPivotKey j).1=k from congrArg Prod.fst hj,
      show (momentPivotKey j).2=p.val from congrArg Prod.snd hj] using h
  have hc : 0<8*(1-a)^k*a^(k%2) := by
    obtain ⟨ha0,ha1⟩ := physical_mem_Ioo a ha
    positivity
  apply moment_kernels_nullspace_columns m (fun i => momentP k i.val a) p _ hP hc
  exact (moment_kernels_candidate_factor a ha m k hk).1

theorem moment_kernel_basis : CanonicalKernelContract ∧ CandidateMomentFactorContract ∧
    MomentPivotContract ∧ CandidateMomentKernelContract :=
  ⟨moment_kernels_canonical_QSR,moment_kernels_candidate_factor,moment_kernels_pivot_nonzero,
    candidate_moment_nullspace⟩

#check moment_kernel_basis
#print axioms moment_kernel_basis
end Blueprint.Thomson.Finite
