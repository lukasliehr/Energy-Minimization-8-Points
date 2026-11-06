import AllS.Units.N_FI.N_upstream_evaluation.N_moment_sums

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

abbrev MomentFreeIndex {m : ℕ} (p : Fin m) := {i : Fin m // i≠p}

def momentNullspaceColumn {m : ℕ} (P : Fin m → ℝ) (p : Fin m) :
    Matrix (Fin m) (MomentFreeIndex p) ℝ := fun i f =>
  (if i=f.val then 1 else 0)-(P f.val/P p)*(if i=p then 1 else 0)

def momentRankOne {m : ℕ} (P : Fin m → ℝ) (c : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => c*P i*P j

def MomentNullspaceContract : Prop := ∀ (m : ℕ) (P : Fin m → ℝ) (p : Fin m) (c : ℝ),
  P p≠0 → 0<c → ∀ M : Matrix (Fin m) (Fin m) ℝ,
  M=(momentRankOne P c) →
    (∀ (f g : MomentFreeIndex p),momentNullspaceColumn P p f.val g=(if f=g then 1 else 0)) ∧
    M*momentNullspaceColumn P p=0 ∧
    (∀ v : Fin m → ℝ,M.mulVec v=0 ↔ ∃ w : MomentFreeIndex p → ℝ,
      (momentNullspaceColumn P p).mulVec w=v) ∧
    Function.Injective (fun w : MomentFreeIndex p → ℝ => (momentNullspaceColumn P p).mulVec w)

theorem momentNullspaceColumn_free {m : ℕ} (P : Fin m → ℝ) (p : Fin m)
    (f g : MomentFreeIndex p) : momentNullspaceColumn P p f.val g=(if f=g then 1 else 0) := by
  simp [momentNullspaceColumn,f.property,Subtype.val_inj]

theorem momentNullspaceColumn_dot {m : ℕ} (P : Fin m → ℝ) (p : Fin m) (hP : P p≠0)
    (f : MomentFreeIndex p) : ∑ i : Fin m,P i*momentNullspaceColumn P p i f=0 := by
  simp only [momentNullspaceColumn,mul_sub,Finset.sum_sub_distrib,mul_ite,mul_one,mul_zero]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  field_simp
  ring

theorem rankOne_mulVec {m : ℕ} (P v : Fin m → ℝ) (c : ℝ) (i : Fin m) :
    (Matrix.mulVec (momentRankOne P c) v) i=c*P i*(∑ j,P j*v j) := by
  simp only [Matrix.mulVec,dotProduct,momentRankOne,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem rankOne_kernel_iff {m : ℕ} (P : Fin m → ℝ) (p : Fin m) (hP : P p≠0)
    (c : ℝ) (hc : 0<c) (v : Fin m → ℝ) :
    Matrix.mulVec (momentRankOne P c) v=0 ↔ ∑ j,P j*v j=0 := by
  constructor
  · intro h
    have hp := congrFun h p
    rw [rankOne_mulVec] at hp
    exact (mul_eq_zero.mp hp).resolve_left (mul_ne_zero (ne_of_gt hc) hP)
  · intro h
    funext i
    rw [rankOne_mulVec,h,mul_zero]
    rfl

theorem momentNullspaceColumn_matrix_zero {m : ℕ} (P : Fin m → ℝ) (p : Fin m)
    (hP : P p≠0) (c : ℝ) : (momentRankOne P c)*momentNullspaceColumn P p=0 := by
  ext i f
  change (∑ j,c*P i*P j*momentNullspaceColumn P p j f)=0
  rw [show (∑ j,c*P i*P j*momentNullspaceColumn P p j f)=
      c*P i*(∑ j,P j*momentNullspaceColumn P p j f) by
    simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj; ring]
  rw [momentNullspaceColumn_dot P p hP,mul_zero]

theorem momentNullspaceColumn_mulVec_free {m : ℕ} (P : Fin m → ℝ) (p : Fin m)
    (w : MomentFreeIndex p → ℝ) (f : MomentFreeIndex p) :
    (momentNullspaceColumn P p).mulVec w f.val=w f := by
  simp only [Matrix.mulVec,dotProduct,momentNullspaceColumn_free,ite_mul,one_mul,zero_mul]
  simp

theorem momentNullspaceColumn_injective {m : ℕ} (P : Fin m → ℝ) (p : Fin m) :
    Function.Injective (fun w : MomentFreeIndex p → ℝ => (momentNullspaceColumn P p).mulVec w) := by
  intro w v h
  funext f
  have hf := congrFun h f.val
  simpa only [momentNullspaceColumn_mulVec_free] using hf

theorem vector_eq_of_free_and_dot {m : ℕ} (P : Fin m → ℝ) (p : Fin m) (hP : P p≠0)
    (v w : Fin m → ℝ) (hfree : ∀ i,i≠p → v i=w i)
    (hdot : ∑ i,P i*v i=∑ i,P i*w i) : v=w := by
  have hz : ∑ i,P i*(v i-w i)=0 := by
    simp only [mul_sub,Finset.sum_sub_distrib,hdot,sub_self]
  have hp : P p*(v p-w p)=0 := by
    rw [Finset.sum_eq_single p] at hz
    · exact hz
    · intro b hb hbp
      simp [hfree b hbp]
    · simp
  have he : v p=w p := sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hP)
  funext i
  by_cases hi : i=p
  · simpa [hi] using he
  · exact hfree i hi

theorem momentNullspaceColumn_range {m : ℕ} (P : Fin m → ℝ) (p : Fin m)
    (hP : P p≠0) (c : ℝ) (hc : 0<c) (v : Fin m → ℝ) :
    Matrix.mulVec (momentRankOne P c) v=0 ↔
      ∃ w : MomentFreeIndex p → ℝ,(momentNullspaceColumn P p).mulVec w=v := by
  have hzero (w : MomentFreeIndex p → ℝ) :
      Matrix.mulVec (momentRankOne P c) ((momentNullspaceColumn P p).mulVec w)=0 := by
    rw [Matrix.mulVec_mulVec,momentNullspaceColumn_matrix_zero P p hP,Matrix.zero_mulVec]
  constructor
  · intro hv
    let w : MomentFreeIndex p → ℝ := fun f => v f.val
    refine ⟨w,vector_eq_of_free_and_dot P p hP _ v ?_ ?_⟩
    · intro i hi
      exact momentNullspaceColumn_mulVec_free P p w ⟨i,hi⟩
    · rw [(rankOne_kernel_iff P p hP c hc _).mp (hzero w),
        (rankOne_kernel_iff P p hP c hc _).mp hv]
  · rintro ⟨w,rfl⟩
    exact hzero w

theorem moment_kernels_nullspace_columns : MomentNullspaceContract := by
  intro m P p c hP hc M hM
  subst M
  exact ⟨momentNullspaceColumn_free P p,momentNullspaceColumn_matrix_zero P p hP c,
    momentNullspaceColumn_range P p hP c hc,momentNullspaceColumn_injective P p⟩

#check moment_kernels_nullspace_columns
#print axioms moment_kernels_nullspace_columns
#check MomentNullspaceContract
#print axioms MomentNullspaceContract
end Blueprint.Thomson.Finite
