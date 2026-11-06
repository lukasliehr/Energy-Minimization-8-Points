import ThomsonNegative.Certificate.Bridges.RawData
import ThomsonNegative.Structure.Coordinates

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure

abbrev SparseEntry := List (Fin 102 × Int)

def sparseCoefficient : SparseEntry → Fin 102 → Int
  | [], _ => 0
  | (i,c)::xs, r => (if r=i then c else 0)+sparseCoefficient xs r

def sparsePolynomial (d : Nat) : SparseEntry → Poly3
  | [] => 0
  | (i,c)::xs => MvPolynomial.C ((c:ℝ)/d)*coordinateMonomial (fullTag i)+sparsePolynomial d xs

lemma synthesize_single (i : Fin 102) (c : ℝ) :
    synthesize (Pi.single i c)=MvPolynomial.C c*coordinateMonomial (fullTag i) := by
  classical
  simp [synthesize,Pi.single_apply,apply_ite,ite_mul]

lemma sparsePolynomial_synthesis (d : Nat) (e : SparseEntry) :
    synthesize (fun r => (sparseCoefficient e r:ℝ)/d)=sparsePolynomial d e := by
  induction e with
  | nil => simp [synthesize,sparseCoefficient,sparsePolynomial]
  | cons t ts ih =>
    rcases t with ⟨i,c⟩
    have hh : (fun r => (sparseCoefficient ((i,c)::ts) r:ℝ)/d)=
        Pi.single i ((c:ℝ)/d)+(fun r => (sparseCoefficient ts r:ℝ)/d) := by
      funext r
      by_cases hr : r=i <;> simp [sparseCoefficient,hr,Pi.single_apply,add_div]
    rw [hh,show synthesize _=synthesizeLinear _ from rfl,map_add]
    change synthesize (Pi.single i ((c:ℝ)/d))+synthesize (fun r => (sparseCoefficient ts r:ℝ)/d)=_
    rw [synthesize_single,ih]
    rfl

def rawCoordinate (b i j : Nat) : Poly3 :=
  synthesize (fun r : Fin 102 => (RawData.coefficient b r.val i j:ℝ)/RawData.denominator b)

lemma rawCoordinate_sparse (b i j : Nat) (e : SparseEntry)
    (h : ∀r : Fin 102,RawData.coefficient b r.val i j=sparseCoefficient e r) :
    rawCoordinate b i j=sparsePolynomial (RawData.denominator b) e := by
  unfold rawCoordinate
  simp_rw [h]
  exact sparsePolynomial_synthesis _ _

end ThomsonNegative.Certificate.Bridges
