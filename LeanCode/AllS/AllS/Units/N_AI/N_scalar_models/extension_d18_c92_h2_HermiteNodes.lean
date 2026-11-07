import AllS.Units.N_AI.N_scalar_models.HermiteSourceSupport
import AllS.Units.N_AI.N_scalar_models.BalancedPotentialSupport
import AllS.Units.N_AI.N_root_models.extension_d18_c92_h2_RootAccepted
import AllS.Units.N_AI.N_data.extension_d18_c92_h2_GramLayout

noncomputable section
namespace Blueprint.CAP.Instances.extension_d18_c92_h2_HermiteNodes
open Blueprint.CAP Blueprint.Thomson.Finite

def exponent (x : ℝ) := extension_d18_c92_h2_RootAccepted.exponent x
def height (x : ℝ) := aS (exponent x)
def multiplicity : Fin 5 → ℕ := extension_d18_c92_h2_GramLayout.multiplicities ∘ sourceNodeOrder
def nodes (x : ℝ) : ℕ → ℝ := expandedProfileNode (sourceNodes (height x)) multiplicity
def rawTag : Fin 19 → Fin 5 := ![0,0,2,2,1,1,1,1,1,1,1,1,1,1,1,1,3,3,4]
def beta (x : ℝ) := balancedMultiplier 92 (exponent x)
def shift (x : ℝ) := balancedShift 92 (exponent x)
def H (x : ℝ) : Polynomial ℝ :=
  Polynomial.C (beta x) *
    hermitePolynomial (exponent x) (height x) extension_d18_c92_h2_GramLayout.multiplicities +
  Polynomial.C (shift x)

theorem total : (∑ i, multiplicity i) = 19 := by decide +kernel

theorem node_eq (x : ℝ) (j : Fin 19) :
    nodes x j.val = sourceContactValues (height x) (rawTag j) := by
  fin_cases j <;> rfl

theorem physical_height (x : ℝ) (hx : x ∈ cellDomain) : physical (height x) :=
  aS_physical _ (extension_d18_c92_h2_RootAccepted.domain x hx).1

theorem exponent_pos (x : ℝ) (hx : x ∈ cellDomain) : 0 < exponent x := by
  have hlo := hx.1
  norm_num [exponent,extension_d18_c92_h2_RootAccepted.exponent,
    ArithmeticPilot.RootControlsAll_extension_d18_c92_h2.center,
    ArithmeticPilot.RootControlsAll_extension_d18_c92_h2.halfwidth]
  linarith

theorem beta_pos (x : ℝ) (hx : x ∈ cellDomain) : 0 < beta x :=
  balancedMultiplier_pos 92 (exponent x) (by norm_num) (exponent_pos x hx)

theorem source_injective (x : ℝ) (hx : x ∈ cellDomain) :
    Function.Injective (sourceNodes (height x)) := by
  rw [sourceNodes_eq_canonical]
  exact (canonicalNodes_strictMono _ (physical_height x hx)).injective.comp
    sourceNodeOrder.injective

theorem grouped (x : ℝ) (hx : x ∈ cellDomain) : GroupedPrefix (nodes x) 19 := by
  have h := expandedProfileNode_grouped _ multiplicity (source_injective x hx)
  rw [total] at h
  exact h

theorem horner_canonical (x : ℝ) (hx : x ∈ cellDomain) :
    sourceNewtonHorner (nodes x)
      (fun i => confluentTable (nodes x) (balancedJet 92 (exponent x)) i 0) 19 0 = H x := by
  have hsource := balancedHermite_affine (sourceNodes (height x)) multiplicity
    92 (exponent x) (source_injective x hx) (by rw [total]; norm_num)
  have hc : profileHermite (sourceNodes (height x)) multiplicity (potentialJet (exponent x)) =
      hermitePolynomial (exponent x) (height x) extension_d18_c92_h2_GramLayout.multiplicities :=
    hermitePolynomial_source_order (exponent x) (height x)
      extension_d18_c92_h2_GramLayout.multiplicities (physical_height x hx)
  rw [hc] at hsource
  change newtonHermite (nodes x) (balancedJet 92 (exponent x)) (∑ i, multiplicity i) = H x at hsource
  rw [total] at hsource
  exact ((newton_hermite_confluent_bridge (nodes x) (balancedJet 92 (exponent x)) 19
    (grouped x hx)).2).trans hsource

#print axioms node_eq
#print axioms beta_pos
#print axioms horner_canonical
end Blueprint.CAP.Instances.extension_d18_c92_h2_HermiteNodes
