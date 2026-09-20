import Thomson8.FastRows

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Thomson8

def SymmetricFunction (f : ℝ → ℝ → ℝ → ℝ) : Prop := ∀ u v t,
  f u v t = f u t v ∧ f u v t = f v u t

theorem SymmetricFunction.mul {f g : ℝ → ℝ → ℝ → ℝ}
    (hf : SymmetricFunction f) (hg : SymmetricFunction g) :
    SymmetricFunction (fun u v t => f u v t * g u v t) := by
  intro u v t
  dsimp only
  exact ⟨by rw [(hf u v t).1,(hg u v t).1],by rw [(hf u v t).2,(hg u v t).2]⟩

theorem SymmetricFunction.const_mul {f : ℝ → ℝ → ℝ → ℝ}
    (hf : SymmetricFunction f) (c : ℝ) : SymmetricFunction (fun u v t => c*f u v t) := by
  intro u v t
  dsimp only
  exact ⟨by rw [(hf u v t).1],by rw [(hf u v t).2]⟩

theorem SymmetricFunction.list_sum {α : Type*} (xs : List α) (f : α → ℝ → ℝ → ℝ → ℝ)
    (hf : ∀ j ∈ xs, SymmetricFunction (f j)) :
    SymmetricFunction (fun u v t => (xs.map fun j => f j u v t).sum) := by
  intro u v t
  dsimp only
  constructor <;> congr 1 <;> apply List.map_congr_left <;> intro j hj
  · exact (hf j hj u v t).1
  · exact (hf j hj u v t).2

theorem SymmetricFunction.symEval {f : ℝ → ℝ → ℝ → ℝ}
    (hf : SymmetricFunction f) (u v t : ℝ) : Poly.symEval f u v t = f u v t := by
  have h1 := (hf u v t).1.symm
  have h2 := (hf u v t).2.symm
  have h3 := (hf t u v).2.trans h1
  have h4 := (hf v u t).1.symm.trans h2
  have h5 := (hf t v u).2.trans h4
  simp only [Poly.symEval,h1,h2,h3,h4,h5]
  ring

theorem s6_symmetry_check (i : Fin 18) :
    (Poly.add (Poly.permute 1 (Data.S6_trivial.polys.getD i []))
      (Poly.scale (K.ofRat (-1)) (Data.S6_trivial.polys.getD i []))).isZero ∧
    (Poly.add (Poly.permute 2 (Data.S6_trivial.polys.getD i []))
      (Poly.scale (K.ofRat (-1)) (Data.S6_trivial.polys.getD i []))).isZero := by
  fin_cases i <;> decide +kernel

theorem s6_polys_symmetric (i : Fin 18) :
    SymmetricFunction (Data.S6_trivial.polys.getD i []).eval := by
  intro u v t
  have h1 := Poly.eval_eq_of_check _ _ (s6_symmetry_check i).1 u v t
  have h2 := Poly.eval_eq_of_check _ _ (s6_symmetry_check i).2 u v t
  rw [Poly.eval_permute ⟨1,by decide⟩] at h1
  rw [Poly.eval_permute ⟨2,by decide⟩] at h2
  exact ⟨h1.symm,h2.symm⟩

def s6PlainRow (i ell : ℕ) : Poly :=
  Poly.mul (Data.S6_trivial.polys.getD i []) (Poly.sum ((List.range 18).map fun j =>
    Poly.scale (Data.S6_trivial.entry i j ell) (Data.S6_trivial.polys.getD j [])))

theorem s6PlainRow_symmetric (i : Fin 18) (ell : ℕ) : SymmetricFunction (s6PlainRow i ell).eval := by
  have hp : (s6PlainRow i ell).eval = fun u v t =>
      (Data.S6_trivial.polys.getD i []).eval u v t *
        ((List.range 18).map fun j => (Data.S6_trivial.entry i j ell).eval *
          (Data.S6_trivial.polys.getD j []).eval u v t).sum := by
    funext u v t
    simp [s6PlainRow,Function.comp_def]
  rw [hp]
  apply (s6_polys_symmetric i).mul
  apply SymmetricFunction.list_sum
  intro j hj
  exact (s6_polys_symmetric ⟨j,List.mem_range.mp hj⟩).const_mul _

theorem s6PlainRow_sound (i : Fin 18) (ell : ℕ) (u v t : ℝ) :
    (Data.S6_trivial.rowComponent i ell).eval u v t = (s6PlainRow i ell).eval u v t := by
  rw [Block.fastRow_eval _ (by rfl)]
  have h : (Data.S6_trivial.fastRow i ell).eval u v t =
      Poly.symEval (s6PlainRow i ell).eval u v t := by
    have hw : Data.S6_trivial.weighted=false := rfl
    have hn : Data.S6_trivial.n=18 := rfl
    simp [Block.fastRow,s6PlainRow,Poly.eval_symmetrize,Poly.symEval,hw,hn]
  rw [h]
  exact (s6PlainRow_symmetric i ell).symEval u v t

#print axioms s6PlainRow_sound

end Thomson8
