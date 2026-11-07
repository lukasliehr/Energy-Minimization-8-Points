import AllS.Units.N_F.N_contact_order
import AllS.Units.N_F.N_definitions
import AllS.Units.N_F.N_potential_jets
import AllS.Units.N_FI.N_newton_hermite.N_power_jets
import Blueprint.FiniteDefinitions
import Blueprint.Target

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

def newtonBasis (z : ℕ → ℝ) (l : ℕ) : Polynomial ℝ :=
  ∏ k ∈ Finset.range l, (Polynomial.X-Polynomial.C (z k))

def priorMultiplicity (z : ℕ → ℝ) (l : ℕ) (x : ℝ) : ℕ := by
  classical
  exact ((Finset.range l).filter (fun k => z k = x)).card

def newtonRemainder (z : ℕ → ℝ) (l : ℕ) (x : ℝ) : Polynomial ℝ := by
  classical
  exact ∏ k ∈ (Finset.range l).filter (fun k => z k ≠ x), (Polynomial.X-Polynomial.C (z k))

theorem newtonBasis_factor (z : ℕ → ℝ) (l : ℕ) (x : ℝ) :
    newtonBasis z l = (Polynomial.X-Polynomial.C x)^(priorMultiplicity z l x) *
      newtonRemainder z l x := by
  classical
  have hE : (∏ k ∈ (Finset.range l).filter (fun k => z k = x),
      (Polynomial.X-Polynomial.C (z k))) =
      (Polynomial.X-Polynomial.C x)^(priorMultiplicity z l x) := by
    calc
      _ = ∏ _k ∈ (Finset.range l).filter (fun k => z k = x),
          (Polynomial.X-Polynomial.C x) := by
        apply Finset.prod_congr rfl
        intro k hk
        rw [(Finset.mem_filter.mp hk).2]
      _ = _ := by simp [priorMultiplicity]
  calc
    newtonBasis z l =
        (∏ k ∈ (Finset.range l).filter (fun k => z k = x),
          (Polynomial.X-Polynomial.C (z k))) * newtonRemainder z l x :=
      (Finset.prod_filter_mul_prod_filter_not (Finset.range l)
        (fun k => z k = x) (fun k => Polynomial.X-Polynomial.C (z k))).symm
    _ = _ := by rw [hE]

theorem newtonRemainder_eval (z : ℕ → ℝ) (l : ℕ) (x : ℝ) :
    (newtonRemainder z l x).eval x =
      ∏ k ∈ (Finset.range l).filter (fun k => z k ≠ x), (x-z k) := by
  classical
  simp [newtonRemainder, Polynomial.eval_prod]

theorem newtonRemainder_eval_ne_zero (z : ℕ → ℝ) (l : ℕ) (x : ℝ) :
    (newtonRemainder z l x).eval x ≠ 0 := by
  classical
  rw [newtonRemainder_eval]
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  exact sub_ne_zero.mpr (Finset.mem_filter.mp hk).2.symm

theorem newtonBasis_degree (z : ℕ → ℝ) (l : ℕ) : (newtonBasis z l).degree = l := by
  rw [newtonBasis, Polynomial.degree_prod_of_monic]
  · simp
  · intro k hk
    exact Polynomial.monic_X_sub_C (z k)

theorem newtonBasis_jet_zero (z : ℕ → ℝ) (l : ℕ) (x : ℝ) (k : ℕ)
    (hk : k < priorMultiplicity z l x) :
    ((Polynomial.derivative^[k]) (newtonBasis z l)).eval x = 0 := by
  rw [newtonBasis_factor z l x]
  exact power_jet_zero x (priorMultiplicity z l x) k (newtonRemainder z l x) hk

theorem newtonBasis_jet_diagonal (z : ℕ → ℝ) (l : ℕ) (x : ℝ) :
    ((Polynomial.derivative^[priorMultiplicity z l x]) (newtonBasis z l)).eval x =
      ((priorMultiplicity z l x).factorial : ℝ)*(newtonRemainder z l x).eval x := by
  rw [newtonBasis_factor z l x]
  exact power_jet_diagonal x (priorMultiplicity z l x) (newtonRemainder z l x)

theorem newtonBasis_jet_diagonal_ne_zero (z : ℕ → ℝ) (l : ℕ) (x : ℝ) :
    ((Polynomial.derivative^[priorMultiplicity z l x]) (newtonBasis z l)).eval x ≠ 0 := by
  rw [newtonBasis_jet_diagonal]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
    (newtonRemainder_eval_ne_zero z l x)

theorem newton_hermite_basis_jet (z : ℕ → ℝ) (l : ℕ) (x : ℝ) :
    (∀ k < priorMultiplicity z l x, ((Polynomial.derivative^[k]) (newtonBasis z l)).eval x = 0) ∧
    ((Polynomial.derivative^[priorMultiplicity z l x]) (newtonBasis z l)).eval x =
      ((priorMultiplicity z l x).factorial : ℝ)*(newtonRemainder z l x).eval x ∧
    ((Polynomial.derivative^[priorMultiplicity z l x]) (newtonBasis z l)).eval x ≠ 0 ∧
    (newtonBasis z l).degree = l :=
  ⟨newtonBasis_jet_zero z l x, newtonBasis_jet_diagonal z l x,
    newtonBasis_jet_diagonal_ne_zero z l x, newtonBasis_degree z l⟩

#check newton_hermite_basis_jet
#print axioms newton_hermite_basis_jet
end Blueprint.Thomson.Finite
