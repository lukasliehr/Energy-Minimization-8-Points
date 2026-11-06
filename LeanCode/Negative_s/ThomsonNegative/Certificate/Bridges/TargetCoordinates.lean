import ThomsonNegative.Certificate.Bridges.RawTables
import ThomsonNegative.Certificate.Bridges.TargetCompatibility
noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure ThomsonNegative.Geometry
set_option maxRecDepth 100000
def targetPowerEntry : Fin 8 → SparseEntry := ![[(0,3)],
  [(1,1)],
  [(2,-2),(3,1)],
  [(4,3),(5,-3),(6,1)],
  [(7,2),(8,4),(9,-4),(10,1)],
  [(11,-5),(12,5),(13,5),(14,-5),(15,1)],
  [(16,3),(17,-2),(18,-12),(19,9),(20,6),(21,-6),(22,1)],
  [(23,7),(24,7),(25,-7),(26,-21),(27,14),(28,7),(29,-7),(30,1)]]
def targetPowerVector (n : Fin 8) : FullSpace := fun ℓ => (sparseCoefficient (targetPowerEntry n) ℓ:ℝ)

lemma targetPowerVector_synthesis (n : Fin 8) :
    synthesize (targetPowerVector n)=coordinatePowerSum n.val := by
  have hh := sparsePolynomial_synthesis 1 (targetPowerEntry n)
  norm_num only [Nat.cast_one,div_one] at hh
  change synthesize (targetPowerVector n)=_ at hh
  rw [hh]
  fin_cases n
  · rw [← powerTable00_eq]
    simp [targetPowerEntry,sparsePolynomial,powerTable00,coordinateMonomial] <;> ring
  · rw [← powerTable01_eq]
    simp [targetPowerEntry,sparsePolynomial,powerTable01,coordinateMonomial] <;> ring
  · rw [← powerTable02_eq]
    simp [targetPowerEntry,sparsePolynomial,powerTable02,coordinateMonomial] <;> ring
  · rw [← powerTable03_eq]
    simp [targetPowerEntry,sparsePolynomial,powerTable03,coordinateMonomial] <;> ring
  · rw [← powerTable04_eq]
    simp [targetPowerEntry,sparsePolynomial,powerTable04,coordinateMonomial] <;> ring
  · rw [← powerTable05_eq]
    simp [targetPowerEntry,sparsePolynomial,powerTable05,coordinateMonomial] <;> ring
  · rw [← powerTable06_eq]
    simp [targetPowerEntry,sparsePolynomial,powerTable06,coordinateMonomial] <;> ring
  · rw [← powerTable07_eq]
    simp [targetPowerEntry,sparsePolynomial,powerTable07,coordinateMonomial] <;> ring
lemma targetPowerVector_physical (n : Fin 8) :
    physicalSynthesize (targetPowerVector n)=rawPowerSum n.val := by
  change invariantSubst (synthesize (targetPowerVector n))=_
  rw [targetPowerVector_synthesis,coordinatePowerSum_subst]

def targetCoefficients (H : Polynomial ℝ) (e : ℝ) : FullSpace :=
  (1/3:ℝ) • (∑ n : Fin 8,H.coeff n.val • targetPowerVector n)-
    (e/28) • Pi.single (0:Fin 102) (1:ℝ)

lemma univariateLift_finite (H : Polynomial ℝ) (hH : H.degree<8) (i : Fin 3) :
    univariateLift i H=∑ n : Fin 8,MvPolynomial.C (H.coeff n.val)*MvPolynomial.X i^n.val := by
  have hn : H.natDegree<8 := by
    by_cases hzero : H=0
    · simp [hzero]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).mpr hH
  conv_lhs => rw [H.as_sum_range_C_mul_X_pow' hn]
  simp only [univariateLift,map_sum,map_mul,Polynomial.aeval_C,map_pow,
    Polynomial.aeval_X,MvPolynomial.algebraMap_eq]
  exact (Fin.sum_univ_eq_sum_range (fun n : Nat => MvPolynomial.C (H.coeff n)*MvPolynomial.X i^n) 8).symm

lemma targetCoefficients_physical (H : Polynomial ℝ) (hH : H.degree<8) (e : ℝ) :
    physicalSynthesize (targetCoefficients H e)=centeredPolynomial H e := by
  simp only [targetCoefficients,map_sub,map_smul,map_sum,targetPowerVector_physical,
    physicalSynthesize_one,smul_eq_mul]
  rw [centeredPolynomial,averagedPolynomial]
  simp only [univariateLift_finite H hH,rawPowerSum,MvPolynomial.smul_eq_C_mul]
  simp only [mul_add,Finset.sum_add_distrib]
  simp

lemma targetCoefficients_compatible (q : ℝ) (hq : 0<q) :
    let a := aStar (2*q-2)
    let v := targetCoefficients (concreteH q a) (auxEnergy q (X a))
    coefficientEll0 a v=0 ∧ coefficientEll1 a v=0 := by
  dsimp
  change ell0 _ (physicalSynthesize _)=0 ∧ ell1 _ (physicalSynthesize _)=0
  rw [targetCoefficients_physical _ (concreteH_degree q _) _]
  exact target_compatibility q hq

lemma targetPower_high : ∀ (n : Fin 8) (j : Fin 35),
    sparseCoefficient (targetPowerEntry n) (highIndex j)=0 := by decide +kernel

lemma targetCoefficients_high (H : Polynomial ℝ) (e : ℝ) (j : Fin 35) :
    targetCoefficients H e (highIndex j)=0 := by
  have hn : highIndex j≠0 := by
    intro he
    have hv := congrArg Fin.val he
    change 67+j.val=0 at hv
    omega
  simp [targetCoefficients,targetPowerVector,targetPower_high,Pi.single_apply,hn]

lemma targetCoefficients_highCompatible (H : Polynomial ℝ) (e : ℝ) :
    HighCompatible (targetCoefficients H e) := by
  intro i
  simp [targetCoefficients_high,highRebuild,highCoordinates]

#print axioms targetCoefficients_physical
#print axioms targetCoefficients_compatible
end ThomsonNegative.Certificate.Bridges
