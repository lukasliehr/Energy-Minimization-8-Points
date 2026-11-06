import AllS.Units.N_F.N_two_squares
import AllS.Units.N_FI.N_congruence.N_isometry

noncomputable section
open Real
namespace Blueprint.Thomson.Finite

def standardFrame : Fin 3 → Point := ![!₂[1,0,0],!₂[0,1,0],!₂[0,0,1]]

def SquareRealization.frame {a : ℝ} {Y : Fin 8 → Point} (S : SquareRealization a Y) : Fin 3 → Point :=
  fun i => S.isometry (standardFrame i)

theorem congruence_upper_frame {a : ℝ} {Y : Fin 8 → Point} (S : SquareRealization a Y) :
    Orthonormal ℝ S.frame ∧ S.center=√a • S.frame 2 ∧
      (Y ∘ S.label)= ![√(1-a) • S.frame 0+√a • S.frame 2,
        √(1-a) • S.frame 1+√a • S.frame 2,
        (-√(1-a)) • S.frame 0+√a • S.frame 2,
        (-√(1-a)) • S.frame 1+√a • S.frame 2] := by
  have hs : Orthonormal ℝ standardFrame := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [PiLp.inner_apply]
    fin_cases i <;> fin_cases j <;>
      norm_num [standardFrame,PiLp.inner_apply,Fin.sum_univ_succ]
  refine ⟨?_,?_,?_⟩
  · rw [orthonormal_iff_ite] at hs ⊢
    intro i j
    exact (S.isometry.inner_map_map _ _).trans (hs i j)
  · change S.isometry (!₂[0,0,√a])=√a • S.isometry (!₂[0,0,1])
    rw [← map_smul]
    congr 1
    ext i
    fin_cases i <;> simp
  · funext i
    change Y (S.label i)=_
    rw [S.points]
    fin_cases i <;> dsimp [SquareRealization.frame,standardFrame,X] <;>
      rw [← map_smul,← map_smul,← map_add] <;> congr 1 <;>
      ext j <;> fin_cases j <;> simp

theorem SquareRealization.center_inner {a : ℝ} {Y : Fin 8 → Point} (S : SquareRealization a Y)
    (ha : 0 ≤ a) (i : Fin 8) (hi : i ∈ S.labels) : inner ℝ S.center (Y i)=a := by
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
  rw [S.points,center,S.isometry.inner_map_map]
  fin_cases j <;> rw [PiLp.inner_apply] <;>
    norm_num [X,Fin.sum_univ_succ,← pow_two,Real.sq_sqrt ha]
  all_goals change √a*√a=a
  all_goals nlinarith [Real.sq_sqrt ha]

#check congruence_upper_frame
#print axioms congruence_upper_frame
end Blueprint.Thomson.Finite
