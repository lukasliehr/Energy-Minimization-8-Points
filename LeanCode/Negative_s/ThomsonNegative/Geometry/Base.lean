import ThomsonNegative.Definitions
import ThomsonNegative.Energy
import ThomsonNegative.Analytic.RootMargin
import ThomsonNegative.Analytic.HermiteSeven

noncomputable section
open Real
open scoped BigOperators
namespace ThomsonNegative.Geometry

abbrev Configuration := Fin 8 → Point
abbrev Poly3 := MvPolynomial (Fin 3) ℝ

def aInf : ℝ := limitingHeight
def physical (a : ℝ) : Prop := aInf < a ∧ a < 1/3

def contacts (a : ℝ) : Fin 4 → ℝ :=
  ![a,2*a-1,-a+(1-a)/√2,-a-(1-a)/√2]

abbrev PairSum := ThomsonNegative.pairSum

def DistinctSum (f : Fin 8 → Fin 8 → Fin 8 → ℝ) : ℝ :=
  ∑ i : Fin 8, ∑ j : Fin 8, ∑ k : Fin 8,
    if i ≠ j ∧ j ≠ k ∧ k ≠ i then f i j k else 0

lemma physical_mem_Ioo (a : ℝ) (ha : physical a) : a ∈ Set.Ioo (0:ℝ) 1 := by
  have h := limitingHeight_range
  change limitingHeight < a ∧ a < 1/3 at ha
  constructor <;> linarith [h.1,ha.1,ha.2]

lemma root_physical (q : ℝ) (hq : 0 < q) : physical (aStar (2*q-2)) := by
  exact aStar_analytic_range (2*q-2) (by linarith)

end ThomsonNegative.Geometry
