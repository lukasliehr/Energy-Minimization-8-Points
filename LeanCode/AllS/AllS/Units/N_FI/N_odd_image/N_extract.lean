import AllS.Units.N_FI.N_image_equality.N_arbitrary_grams
import AllS.Units.N_F.N_zero_tensors

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem candidate_odd_momentP (a : ℝ) : momentP 0 1 a=0 ∧ momentP 0 3 a=0 := by
  have hq : (1/Real.sqrt 2)^2=(1/2 : ℝ) := by norm_num [div_pow,Real.sq_sqrt]
  constructor
  · simp [momentP,contacts]
    ring
  · change 1+2*a^3+(2*a-1)^3+2*(-a+(1-a)/Real.sqrt 2)^3+2*(-a-(1-a)/Real.sqrt 2)^3=0
    linear_combination (-12*a*(1-a)^2)*hq

theorem canonicalMoment_zero_diagonal (m : ℕ) (Y : Configuration) (r : Fin m) :
    canonicalMoment m 0 Y r r=∑ i : Fin 8,(∑ j : Fin 8,(inner ℝ (Y i) (Y j))^r.val)^2 := by
  rw [canonicalMoment_eq_generic,GenericMoments.momentMatrix_entry]
  simp only [GenericMoments.tripleSum,GenericMoments.onTriples,GenericMoments.kernelQ,mul_one,pow_two,
    Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]

theorem zero_compressed_moment_diagonal (a : ℝ) (d : ℕ) (hd : 0<d)
    (p : MomentPivots d) (Y : Configuration) (hY : ∀ i,‖Y i‖=1)
    (r : Fin (d+1)) (hr : momentP 0 r.val a=0)
    (hp : momentP 0 (p ⟨0,hd⟩).val a≠0)
    (hz : gramBlockMoment Y a d p (.inl ⟨0,hd⟩)=0) : canonicalMoment (d+1) 0 Y r r=0 := by
  let k : Fin d := ⟨0,hd⟩
  have hrp : r≠p k := by
    intro he
    apply hp
    simpa only [he] using hr
  let f : MomentFreeIndex (p k) := ⟨r,hrp⟩
  let j : Fin d := (finSuccAboveEquiv (p k)).symm f
  have hB (i : Fin (d+1)) : momentKernelMatrix a d p k i j=(if i=r then 1 else 0) := by
    simp only [momentKernelMatrix,j,Equiv.apply_symm_apply,momentNullspaceColumn,f]
    simp only [k,hr,zero_div,zero_mul,sub_zero]
  have he := gramBlockMoment_moment Y hY a d p k
  rw [hz] at he
  have hj := congrFun (congrFun he j) j
  change (0 : ℝ)=6*((momentKernelMatrix a d p k).transpose*canonicalMoment (d+1) 0 Y*
    momentKernelMatrix a d p k) j j at hj
  simp only [Matrix.mul_apply,Matrix.transpose_apply,hB,mul_ite,ite_mul,mul_one,one_mul,mul_zero,zero_mul,
    Finset.sum_ite_eq',Finset.mem_univ,if_true] at hj
  linarith

theorem certificate_vertex_odd_moments {s a : ℝ} {D : ℕ} {m : Fin 5 → ℕ}
    (h : Certificate s a D m) (Y : Configuration) (hY : IsConfiguration Y)
    (he : E s Y=E s (X a)) :
    ∀ i,(∑ j,inner ℝ (Y i) (Y j))=0 ∧ (∑ j,(inner ℝ (Y i) (Y j))^3)=0 := by
  obtain ⟨p,β,W,hp,hβ,hW,hpoly⟩ := h.witness
  have hd := (activeDegree_half h.degree_active).1
  have hk : 0<D/2 := by omega
  have hp0 : momentP 0 (p ⟨0,hk⟩).val a≠0 := by
    obtain ⟨j,hj⟩ := hp ⟨0,hk⟩
    have hn := (moment_kernels_pivot_nonzero a h.physical_a j).2
    simpa only [show (momentPivotKey j).1=0 from congrArg Prod.fst hj,
      show (momentPivotKey j).2=(p ⟨0,hk⟩).val from congrArg Prod.snd hj] using hn
  have hblock := equality_block_moment_zero h Y hY he p β W hW hpoly (.inl ⟨0,hk⟩)
  have h1 := zero_compressed_moment_diagonal a (D/2) hk p Y hY.1
    ⟨1,by omega⟩ (candidate_odd_momentP a).1 hp0 hblock
  have h3 := zero_compressed_moment_diagonal a (D/2) hk p Y hY.1
    ⟨3,by omega⟩ (candidate_odd_momentP a).2 hp0 hblock
  rw [canonicalMoment_zero_diagonal] at h1 h3
  intro i
  have hi1 := (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => sq_nonneg _)).mp h1 i (Finset.mem_univ _)
  have hi3 := (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => sq_nonneg _)).mp h3 i (Finset.mem_univ _)
  exact ⟨by simpa using (sq_eq_zero_iff.mp hi1),by simpa using (sq_eq_zero_iff.mp hi3)⟩

def OddImageExtractContract : Prop := ∀ s a D m,Certificate s a D m →
  ∀ Y : Configuration,IsConfiguration Y → E s Y=E s (X a) →
    (∑ i,Y i)=0 ∧ oddMoment 3 Y=0 ∧
      ∀ i,(∑ j,inner ℝ (Y i) (Y j))=0 ∧ (∑ j,(inner ℝ (Y i) (Y j))^3)=0

theorem odd_image_extract : OddImageExtractContract := by
  intro s a D m h Y hY he
  have ho := certificate_vertex_odd_moments h Y hY he
  have ht := (zero_tensors_equivalence Y).mp ho
  exact ⟨ht.1,ht.2,ho⟩

#check odd_image_extract
#print axioms odd_image_extract
end Blueprint.Thomson.Finite
