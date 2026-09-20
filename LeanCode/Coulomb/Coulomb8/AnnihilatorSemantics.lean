import Coulomb8.IntegerPolynomial

namespace Coulomb8
open scoped BigOperators

theorem scaled_annihilator {n : ℕ} (L Q : Fin n → IP) (p : Fin n → K) (c : ℚ) (d : ℝ)
    (hs : List.ofFn p=List.ofFn (fun i => K.scale c (Q i).toK))
    (hz : (IP.dot (List.ofFn L) (List.ofFn Q)).isZero) :
    ∑ i, (IP.eval (L i)/d)*K.eval (p i)=0 := by
  have h := IP.annihilator_of_check L Q hz
  calc
    _ = ((c : ℝ)/d)*∑ i, IP.eval (L i)*IP.eval (Q i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [IP.eval_scaled_ofFn p Q c hs]
      ring
    _ = 0 := by rw [h,mul_zero]

end Coulomb8

#print axioms Coulomb8.scaled_annihilator
