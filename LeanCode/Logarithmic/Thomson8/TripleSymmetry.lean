import Thomson8.TripleSums
import Thomson8.Symmetry
import Thomson8.GeometryBasics

namespace Thomson8

open scoped InnerProductSpace

noncomputable def indexSym (f : Index → Index → Index → ℝ) (i j k : Index) : ℝ :=
  (f i j k+f i k j+f j i k+f k i j+f j k i+f k j i)/6

theorem tripleSum_indexSym (f : Index → Index → Index → ℝ) :
    tripleSum (indexSym f)=tripleSum f := by
  have h312 : tripleSum (fun i j k => f k i j)=tripleSum f :=
    (tripleSum_swap23 (fun i j k => f j i k)).trans (tripleSum_swap12 f)
  have h231 : tripleSum (fun i j k => f j k i)=tripleSum f :=
    (tripleSum_swap12 (fun i j k => f i k j)).trans (tripleSum_swap23 f)
  have h321 : tripleSum (fun i j k => f k j i)=tripleSum f :=
    (tripleSum_swap12 (fun i j k => f k i j)).trans h312
  have hsplit : tripleSum (indexSym f) =
      (tripleSum f+tripleSum (fun i j k => f i k j)+tripleSum (fun i j k => f j i k)+
        tripleSum (fun i j k => f k i j)+tripleSum (fun i j k => f j k i)+
        tripleSum (fun i j k => f k j i))/6 := by
    simp only [tripleSum,indexSym]
    simp_rw [← Finset.sum_div,Finset.sum_add_distrib]
  rw [hsplit,tripleSum_swap12 f,tripleSum_swap23 f,h312,h231,h321]
  ring

theorem distinctSum_indexSym (f : Index → Index → Index → ℝ) :
    distinctSum (indexSym f)=distinctSum f := by
  have h312 : distinctSum (fun i j k => f k i j)=distinctSum f :=
    (distinctSum_swap23 (fun i j k => f j i k)).trans (distinctSum_swap12 f)
  have h231 : distinctSum (fun i j k => f j k i)=distinctSum f :=
    (distinctSum_swap12 (fun i j k => f i k j)).trans (distinctSum_swap23 f)
  have h321 : distinctSum (fun i j k => f k j i)=distinctSum f :=
    (distinctSum_swap12 (fun i j k => f k i j)).trans h312
  have hsplit : distinctSum (indexSym f) =
      (distinctSum f+distinctSum (fun i j k => f i k j)+distinctSum (fun i j k => f j i k)+
        distinctSum (fun i j k => f k i j)+distinctSum (fun i j k => f j k i)+
        distinctSum (fun i j k => f k j i))/6 := by
    have he (p : Prop) [Decidable p] (a b c d e g : ℝ) :
        (if p then (a+b+c+d+e+g)/6 else 0) =
          ((if p then a else 0)+(if p then b else 0)+(if p then c else 0)+
            (if p then d else 0)+(if p then e else 0)+(if p then g else 0))/6 := by
      split_ifs <;> ring
    simp only [distinctSum,indexSym,he]
    simp_rw [← Finset.sum_div,Finset.sum_add_distrib]
  rw [hsplit,distinctSum_swap12 f,distinctSum_swap23 f,h312,h231,h321]
  ring

noncomputable def onTriples (x : Configuration) (f : ℝ → ℝ → ℝ → ℝ)
    (i j k : Index) : ℝ := f ⟪x i,x j⟫_ℝ ⟪x i,x k⟫_ℝ ⟪x j,x k⟫_ℝ

theorem onTriples_sym (x : Configuration) (f : ℝ → ℝ → ℝ → ℝ) :
    onTriples x (Poly.symEval f) = indexSym (onTriples x f) := by
  funext i j k
  simp only [onTriples,Poly.symEval,indexSym,real_inner_comm (x k) (x i),
    real_inner_comm (x j) (x i),real_inner_comm (x k) (x j)]
  ring

theorem tripleSum_sym (x : Configuration) (f : ℝ → ℝ → ℝ → ℝ) :
    tripleSum (onTriples x (Poly.symEval f)) = tripleSum (onTriples x f) := by
  rw [onTriples_sym,tripleSum_indexSym]

theorem distinctSum_sym (x : Configuration) (f : ℝ → ℝ → ℝ → ℝ) :
    distinctSum (onTriples x (Poly.symEval f)) = distinctSum (onTriples x f) := by
  rw [onTriples_sym,distinctSum_indexSym]

end Thomson8
