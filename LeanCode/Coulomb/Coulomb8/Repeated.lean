import Coulomb8.Certificate

namespace Coulomb8.Poly

theorem eval_repeated_zero (p : Poly) (u v t : ℝ) :
    (repeated 0 p).eval u v t = p.eval u u 1 := by
  induction p with
  | nil => simp [repeated]
  | cons h p ih =>
    rcases h with ⟨a,c⟩
    simp [repeated,Exponent.eval,pow_add] at ih ⊢
    rw [ih]

theorem eval_repeated_one (p : Poly) (u v t : ℝ) :
    (repeated 1 p).eval u v t = p.eval v v 1 := by
  induction p with
  | nil => simp [repeated]
  | cons h p ih =>
    rcases h with ⟨a,c⟩
    simp [repeated,Exponent.eval,pow_add] at ih ⊢
    rw [ih]

theorem eval_repeated_two (p : Poly) (u v t : ℝ) :
    (repeated 2 p).eval u v t = p.eval t t 1 := by
  induction p with
  | nil => simp [repeated]
  | cons h p ih =>
    rcases h with ⟨a,c⟩
    simp [repeated,Exponent.eval,pow_add] at ih ⊢
    rw [ih]

end Coulomb8.Poly
