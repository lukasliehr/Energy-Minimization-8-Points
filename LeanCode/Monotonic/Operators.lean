import LeanCode.Monotonic.Basic

noncomputable section
open Real Set
open scoped BigOperators
namespace SquareAntiprismCounterexample

def B (a : ℝ) : ℝ := 2*a-1
def C (a : ℝ) : ℝ := -a+(1-a)/√2
def D (a : ℝ) : ℝ := -a-(1-a)/√2
def kPlus : ℝ := 1+1/√2
def kMinus : ℝ := 1-1/√2

def L (a : ℝ) (p : ℝ → ℝ) : ℝ :=
  -16*p (dA a)-16*p (dB a)+8*(2+√2)*p (dC a)+8*(2-√2)*p (dD a)

def Q (a : ℝ) (p q : ℝ → ℝ) : ℝ :=
  16*(p (dA a)+B a*p (dB a)+C a*p (dC a)+D a*p (dD a)) +
  128*a*(1-a)*q (dB a) +
  32*a*(1-a)*(kPlus^2*q (dC a)+kMinus^2*q (dD a))

def familySecond (a : ℝ) (q : ℝ → ℝ) : ℝ :=
  32*q (dA a)+64*q (dB a)+8*(2+√2)^2*q (dC a)+8*(2-√2)^2*q (dD a)

lemma L_add (a : ℝ) (p r : ℝ → ℝ) :
    L a (fun t => p t+r t) = L a p + L a r := by unfold L; ring
lemma L_smul (a c : ℝ) (p : ℝ → ℝ) :
    L a (fun t => c*p t) = c*L a p := by unfold L; ring
lemma Q_add (a : ℝ) (p q r s : ℝ → ℝ) :
    Q a (fun t => p t+r t) (fun t => q t+s t) = Q a p q + Q a r s := by unfold Q; ring
lemma Q_smul (a c : ℝ) (p q : ℝ → ℝ) :
    Q a (fun t => c*p t) (fun t => c*q t) = c*Q a p q := by unfold Q; ring
lemma L_constant (a c : ℝ) : L a (fun _ => c) = 0 := by unfold L; ring
lemma Q_constant (a c : ℝ) : Q a (fun _ => c) (fun _ => 0) = 0 := by
  unfold Q B C D; ring

lemma L_quadratic (a : ℝ) : L a (fun t => 2*t) = 128*(3*a-1) := by
  unfold L dA dB dC dD
  ring_nf
  rw [sqrt_two_sq]
  ring

lemma Q_quadratic (a : ℝ) : Q a (fun t => 2*t) (fun _ => 2) = 128*(6*a-7*a^2-1) := by
  unfold Q B C D kPlus kMinus dA dB dC dD
  simp only [div_eq_mul_inv, inv_sqrt_two]
  ring_nf
  simp only [sqrt_two_sq]
  ring

lemma L_quadratic_star : L aStar (fun t => 2*t) = -64/3 := by
  rw [L_quadratic]; norm_num [aStar]
lemma QL_quadratic_star : Q aStar (fun t => 2*t) (fun _ => 2) +
    L aStar (fun t => 2*t) = -416/81 := by
  rw [L_quadratic, Q_quadratic]; norm_num [aStar]

end SquareAntiprismCounterexample
