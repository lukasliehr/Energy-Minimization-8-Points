import Coulomb8.Certificate
import Coulomb8.Symmetry

namespace Coulomb8.Block

def weight (b : Block) : Poly :=
  if b.weighted then
    Poly.add (Poly.const K.one) (Poly.scale (K.ofRat (-1)) (Poly.monomial ⟨2,0,0⟩))
    else Poly.const K.one

def weightedProduct (b : Block) (i j : ℕ) : Poly :=
  Poly.mul b.weight (Poly.mul (b.polys.getD i []) (b.polys.getD j []))

theorem mul_chunk_cached (first rest right tail result : Poly)
    (ht : ∀ u v t, (Poly.mul rest right).eval u v t=tail.eval u v t)
    (hc : (Poly.add (Poly.add (Poly.mul first right) tail)
      (Poly.scale (K.ofRat (-1)) result)).isZero) (u v t : ℝ) :
    (Poly.mul (first++rest) right).eval u v t=result.eval u v t := by
  have happ : (first++rest).eval u v t=first.eval u v t+rest.eval u v t := by
    simp [Poly.eval,List.map_append,List.sum_append]
  calc
    _ = (Poly.mul first right).eval u v t+(Poly.mul rest right).eval u v t := by
      simp only [Poly.eval_mul,happ]
      ring
    _ = (Poly.add (Poly.mul first right) tail).eval u v t := by
      rw [ht,Poly.eval_add]
    _ = _ := Poly.eval_eq_of_check _ _ hc u v t

theorem sos_cached_sound_of_eq (b : Block) (hb : b.moment=false) (i j : ℕ)
    (cached result : Poly)
    (hp : ∀ u v t, (b.weightedProduct i j).eval u v t=cached.eval u v t)
    (hs : (Poly.add (Poly.scale (K.ofRat (if i=j then 1 else 2)) (Poly.symmetrize cached))
      (Poly.scale (K.ofRat (-1)) result)).isZero) (u v t : ℝ) :
    (b.upperColumn i j).eval u v t=result.eval u v t := by
  have hfun : (b.weightedProduct i j).eval=cached.eval := funext fun u => funext fun v => funext (hp u v)
  have he : (b.upperColumn i j).eval u v t =
      (Poly.scale (K.ofRat (if i=j then 1 else 2)) (Poly.symmetrize cached)).eval u v t := by
    simp only [upperColumn,column,hb,Bool.false_eq_true,if_false,Poly.eval_scale,
      Poly.eval_symmetrize]
    change _ * Poly.symEval (b.weightedProduct i j).eval u v t = _
    rw [hfun]
  exact he.trans (Poly.eval_eq_of_check _ _ hs u v t)

theorem sos_cached_sound (b : Block) (hb : b.moment=false) (i j : ℕ)
    (cached result : Poly)
    (hp : (Poly.add (b.weightedProduct i j) (Poly.scale (K.ofRat (-1)) cached)).isZero)
    (hs : (Poly.add (Poly.scale (K.ofRat (if i=j then 1 else 2)) (Poly.symmetrize cached))
      (Poly.scale (K.ofRat (-1)) result)).isZero) (u v t : ℝ) :
    (b.upperColumn i j).eval u v t=result.eval u v t := by
  exact sos_cached_sound_of_eq b hb i j cached result
    (fun u v t => Poly.eval_eq_of_check _ _ hp u v t) hs u v t

end Coulomb8.Block

namespace Coulomb8.Block

theorem sos_scaled_product (b : Block) (i j : ℕ) (c d : ℚ)
    (left right product cached : Poly)
    (hl : ∀ u v t, (b.polys.getD i []).eval u v t=(Poly.scale (K.ofRat c) left).eval u v t)
    (hr : ∀ u v t, (b.polys.getD j []).eval u v t=(Poly.scale (K.ofRat d) right).eval u v t)
    (hp : ∀ u v t, (Poly.mul left right).eval u v t=product.eval u v t)
    (hc : (Poly.add (Poly.scale (K.ofRat (c*d)) (Poly.mul b.weight product))
      (Poly.scale (K.ofRat (-1)) cached)).isZero) (u v t : ℝ) :
    (b.weightedProduct i j).eval u v t=cached.eval u v t := by
  have hh := Poly.eval_eq_of_check _ _ hc u v t
  simp only [weightedProduct,Poly.eval_mul,hl,hr,Poly.eval_scale,K.eval_ofRat]
  have hpv := hp u v t
  rw [Poly.eval_mul] at hpv
  simp only [Poly.eval_scale,Poly.eval_mul,K.eval_ofRat,Rat.cast_mul] at hh
  rw [←hpv] at hh
  convert hh using 1 <;> ring

end Coulomb8.Block
