import AllS.Units.N_GI.N_disphenoid.N_hadamard_frame
import Mathlib.Analysis.InnerProductSpace.Orthonormal

set_option maxHeartbeats 1200000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

def hadamardVectors (A : Fin 4 → Point) : Fin 3 → Point :=
  ![hadamardU A,hadamardV A,hadamardW A]

def cubeSign : Fin 4 → Fin 3 → ℝ := ![![1,1,1],![1,-1,-1],![-1,1,-1],![-1,-1,1]]

def normalizedFrame (v : Fin 3 → Point) (i : Fin 3) : Point := ‖v i‖⁻¹ • v i

theorem normalizedFrame_orthonormal (v : Fin 3 → Point) (hn : ∀i,v i≠0)
    (ho : Pairwise (fun i j => inner ℝ (v i) (v j)=0)) : Orthonormal ℝ (normalizedFrame v) := by
  constructor
  · intro i
    simp only [normalizedFrame,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hn i))
  · intro i j hij
    simp only [normalizedFrame,inner_smul_left,inner_smul_right,conj_trivial,ho hij,mul_zero]

theorem normalizedFrame_rescale (v : Fin 3 → Point) (hn : ∀i,v i≠0) (i : Fin 3) :
    ‖v i‖ • normalizedFrame v i=v i := by
  rw [normalizedFrame,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hn i)),one_smul]

theorem hadamard_reconstruct (A : Fin 4 → Point) (i : Fin 4) :
    A i=hadamardG A+∑k,cubeSign i k • hadamardVectors A k := by
  rw [Fin.sum_univ_three]
  fin_cases i <;> simp [cubeSign,hadamardVectors,hadamardG,hadamardU,hadamardV,hadamardW] <;> module

theorem hadamard_zero_iff_sum_zero (A : Fin 4 → Point) : hadamardG A=0 ↔ ∑i,A i=0 := by
  rw [hadamardG,←Fin.sum_univ_four,smul_eq_zero]
  norm_num

theorem hadamardVectors_nonzero_orthogonal (A : Fin 4 → Point)
    (huv : inner ℝ (hadamardU A) (hadamardV A)=0)
    (huw : inner ℝ (hadamardU A) (hadamardW A)=0)
    (hvw : inner ℝ (hadamardV A) (hadamardW A)=0)
    (hun : hadamardU A≠0) (hvn : hadamardV A≠0) (hwn : hadamardW A≠0) :
    (∀i,hadamardVectors A i≠0) ∧
    Pairwise (fun i j => inner ℝ (hadamardVectors A i) (hadamardVectors A j)=0) := by
  constructor
  · intro i
    fin_cases i <;> simp [hadamardVectors,hun,hvn,hwn]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [hadamardVectors,real_inner_comm]

#print axioms hadamard_reconstruct
#print axioms normalizedFrame_orthonormal
#print axioms hadamardVectors_nonzero_orthogonal
end Blueprint.Thomson.Tail.Implementation
