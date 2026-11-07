import AllS.Units.N_GI.N_disphenoid.N_normalized_frame

set_option maxHeartbeats 1200000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem cubeSign_dot (i j : Fin 4) :
    (∑k,cubeSign i k*cubeSign j k)=if i=j then (3:ℝ) else -1 := by
  rw [Fin.sum_univ_three]
  fin_cases i <;> fin_cases j
  · change (1*1+1*1+1*1 : ℝ) = if (0 : Fin 4)=0 then 3 else -1
    norm_num <;> decide
  · change (1*1+1*(-1)+1*(-1) : ℝ) = if (0 : Fin 4)=1 then 3 else -1
    norm_num <;> decide
  · change (1*(-1)+1*1+1*(-1) : ℝ) = if (0 : Fin 4)=2 then 3 else -1
    norm_num <;> decide
  · change (1*(-1)+1*(-1)+1*1 : ℝ) = if (0 : Fin 4)=3 then 3 else -1
    norm_num <;> decide
  · change (1*1+(-1)*1+(-1)*1 : ℝ) = if (1 : Fin 4)=0 then 3 else -1
    norm_num <;> decide
  · change (1*1+(-1)*(-1)+(-1)*(-1) : ℝ) = if (1 : Fin 4)=1 then 3 else -1
    norm_num <;> decide
  · change (1*(-1)+(-1)*1+(-1)*(-1) : ℝ) = if (1 : Fin 4)=2 then 3 else -1
    norm_num <;> decide
  · change (1*(-1)+(-1)*(-1)+(-1)*1 : ℝ) = if (1 : Fin 4)=3 then 3 else -1
    norm_num <;> decide
  · change ((-1)*1+1*1+(-1)*1 : ℝ) = if (2 : Fin 4)=0 then 3 else -1
    norm_num <;> decide
  · change ((-1)*1+1*(-1)+(-1)*(-1) : ℝ) = if (2 : Fin 4)=1 then 3 else -1
    norm_num <;> decide
  · change ((-1)*(-1)+1*1+(-1)*(-1) : ℝ) = if (2 : Fin 4)=2 then 3 else -1
    norm_num <;> decide
  · change ((-1)*(-1)+1*(-1)+(-1)*1 : ℝ) = if (2 : Fin 4)=3 then 3 else -1
    norm_num <;> decide
  · change ((-1)*1+(-1)*1+1*1 : ℝ) = if (3 : Fin 4)=0 then 3 else -1
    norm_num <;> decide
  · change ((-1)*1+(-1)*(-1)+1*(-1) : ℝ) = if (3 : Fin 4)=1 then 3 else -1
    norm_num <;> decide
  · change ((-1)*(-1)+(-1)*1+1*(-1) : ℝ) = if (3 : Fin 4)=2 then 3 else -1
    norm_num <;> decide
  · change ((-1)*(-1)+(-1)*(-1)+1*1 : ℝ) = if (3 : Fin 4)=3 then 3 else -1
    norm_num <;> decide

theorem hadamard_orthonormal_coordinates (A : Fin 4 → Point)
    (hG : hadamardG A=0)
    (hn : ∀i,hadamardVectors A i≠0)
    (ho : Pairwise (fun i j => inner ℝ (hadamardVectors A i) (hadamardVectors A j)=0)) :
    ∃ (e : Fin 3 → Point) (x : Fin 3 → ℝ),Orthonormal ℝ e ∧ (∀k,0<x k) ∧
      ∀i,A i=∑k,(cubeSign i k*x k) • e k := by
  let v := hadamardVectors A
  refine ⟨normalizedFrame v,fun k => ‖v k‖,normalizedFrame_orthonormal v hn ho,
    fun k => norm_pos_iff.mpr (hn k),fun i => ?_⟩
  rw [hadamard_reconstruct A i,hG,zero_add]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_smul,normalizedFrame_rescale v hn k]

theorem cube_dual_candidate_inner (e : Fin 3 → Point) (he : Orthonormal ℝ e)
    (x : Fin 3 → ℝ) (hx : ∀k,0<x k) (c : ℝ) (i j : Fin 4) :
    inner ℝ (∑k,(-c*cubeSign i k/x k) • e k) (∑k,(cubeSign j k*x k) • e k)=
      -c*(if i=j then 3 else -1) := by
  rw [he.inner_sum]
  simp only [conj_trivial]
  calc
    ∑k,(-c*cubeSign i k/x k)*(cubeSign j k*x k) =
        ∑k,-c*(cubeSign i k*cubeSign j k) := by
      apply Finset.sum_congr rfl
      intro k _
      field_simp [(hx k).ne']
      <;> ring
    _ = -c*(∑k,cubeSign i k*cubeSign j k) := by rw [Finset.mul_sum]
    _ = _ := by rw [cubeSign_dot]

theorem cube_dual_coordinates (A B : Fin 4 → Point) (c : ℝ) (hc : 0<c)
    (hAunit : ∀i,‖A i‖=1) (hAinj : Function.Injective A)
    (hcross : ∀i j,i≠j → inner ℝ (A i) (B j)=c)
    (e : Fin 3 → Point) (he : Orthonormal ℝ e) (x : Fin 3 → ℝ) (hx : ∀k,0<x k)
    (hA : ∀i,A i=∑k,(cubeSign i k*x k) • e k) :
    ∀i,B i=∑k,(-c*cubeSign i k/x k) • e k := by
  intro i
  have hLI := polar_tetrahedra_facet_independent A B c hAunit hAinj hc hcross i.succAbove Fin.succAbove_right_injective
  apply normal_eq_of_independent_triple (A ∘ i.succAbove) hLI
  intro j
  change inner ℝ (B i) (A (i.succAbove j))=inner ℝ (∑k,(-c*cubeSign i k/x k) • e k) (A (i.succAbove j))
  have hb : inner ℝ (B i) (A (i.succAbove j))=c :=
    (real_inner_comm _ _).trans (hcross _ i (Fin.succAbove_ne i j))
  rw [hb,hA,cube_dual_candidate_inner e he x hx c i (i.succAbove j),if_neg (Fin.succAbove_ne i j).symm]
  ring

#print axioms hadamard_orthonormal_coordinates
#print axioms cube_dual_coordinates
end Blueprint.Thomson.Tail.Implementation
