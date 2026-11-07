import AllS.Units.N_AI.N_encoding.N_list_evaluation
import AllS.Units.N_FI.N_contact_order.N_packing_bounds

noncomputable section
namespace Blueprint.CAP

def evalRationalList : List ℚ → ℝ → ℝ
  | [],_ => 0
  | c::p,a => (c:ℝ)+a*evalRationalList p a

theorem evalRationalList_eq (p : List ℚ) (a : ℝ) :
    evalRationalList p a=(listPolynomial p).eval₂ (Rat.castHom ℝ) a := by
  induction p with
  | nil => simp [evalRationalList,listPolynomial_nil]
  | cons c p ih => simp [evalRationalList,listPolynomial_cons,ih]

#print axioms evalRationalList_eq
end Blueprint.CAP
