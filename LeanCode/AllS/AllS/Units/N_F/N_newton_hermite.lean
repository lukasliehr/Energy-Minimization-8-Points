import AllS.Units.N_F.N_contact_order
import AllS.Units.N_F.N_definitions
import AllS.Units.N_F.N_potential_jets
import AllS.Units.N_FI.N_newton_hermite.N_basis_jet
import AllS.Units.N_FI.N_newton_hermite.N_confluent_bridge
import AllS.Units.N_FI.N_newton_hermite.N_divided_difference_monomials
import AllS.Units.N_FI.N_newton_hermite.N_polynomial_newton
import AllS.Units.N_FI.N_newton_hermite.N_power_jets
import AllS.Units.N_FI.N_newton_hermite.N_stage_invariant
import AllS.Units.N_FI.N_newton_hermite.N_unique
import AllS.Units.N_FI.N_newton_hermite.N_zero_jets_divisible
import Blueprint.FiniteDefinitions
import Blueprint.Target

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

/-- The cumulative boundaries of the five repeated-node blocks. -/
def profileOffset (m : Fin 5 → ℕ) : Fin 6 → ℕ :=
  ![0, m 0, m 0+m 1, m 0+m 1+m 2, m 0+m 1+m 2+m 3,
    m 0+m 1+m 2+m 3+m 4]

/-- Label of the k-th expanded node; only k<sum m is consumed. -/
def profileLabel (m : Fin 5 → ℕ) (k : ℕ) : Fin 5 :=
  if k < profileOffset m 1 then 0 else
  if k < profileOffset m 2 then 1 else
  if k < profileOffset m 3 then 2 else
  if k < profileOffset m 4 then 3 else 4

def expandedProfileNode (z : Fin 5 → ℝ) (m : Fin 5 → ℕ) (k : ℕ) : ℝ :=
  z (profileLabel m k)

def profileHermite (z : Fin 5 → ℝ) (m : Fin 5 → ℕ) (J : ℕ → ℝ → ℝ) : Polynomial ℝ :=
  newtonHermite (expandedProfileNode z m) J (∑ i, m i)

theorem profile_total (m : Fin 5 → ℕ) :
    (∑ i, m i) = m 0+m 1+m 2+m 3+m 4 := by
  simp only [Fin.sum_univ_succ]
  change m 0+(m 1+(m 2+(m 3+(m 4+0)))) = m 0+m 1+m 2+m 3+m 4
  omega

theorem profileLabel_val (m : Fin 5 → ℕ) (k : ℕ) :
    (profileLabel m k).val = if k < profileOffset m 1 then 0 else
      if k < profileOffset m 2 then 1 else
      if k < profileOffset m 3 then 2 else
      if k < profileOffset m 4 then 3 else 4 := by
  unfold profileLabel
  split_ifs <;> rfl

theorem profileLabel_cases (m : Fin 5 → ℕ) (k : ℕ) :
    (profileLabel m k = 0 ∧ k < profileOffset m 1) ∨
    (profileLabel m k = 1 ∧ profileOffset m 1 ≤ k ∧ k < profileOffset m 2) ∨
    (profileLabel m k = 2 ∧ profileOffset m 2 ≤ k ∧ k < profileOffset m 3) ∨
    (profileLabel m k = 3 ∧ profileOffset m 3 ≤ k ∧ k < profileOffset m 4) ∨
    (profileLabel m k = 4 ∧ profileOffset m 4 ≤ k) := by
  by_cases h₀ : k < profileOffset m 1
  · exact Or.inl ⟨by rw [profileLabel, if_pos h₀], h₀⟩
  by_cases h₁ : k < profileOffset m 2
  · exact Or.inr (Or.inl ⟨by rw [profileLabel, if_neg h₀, if_pos h₁], by omega, h₁⟩)
  by_cases h₂ : k < profileOffset m 3
  · exact Or.inr (Or.inr (Or.inl ⟨by rw [profileLabel, if_neg h₀, if_neg h₁, if_pos h₂], by omega, h₂⟩))
  by_cases h₃ : k < profileOffset m 4
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨by rw [profileLabel, if_neg h₀, if_neg h₁, if_neg h₂, if_pos h₃], by omega, h₃⟩)))
  exact Or.inr (Or.inr (Or.inr (Or.inr
    ⟨by rw [profileLabel, if_neg h₀, if_neg h₁, if_neg h₂, if_neg h₃], by omega⟩)))

theorem profileLabel_monotone (m : Fin 5 → ℕ) : Monotone (profileLabel m) := by
  intro i j hij
  rcases profileLabel_cases m i with ⟨hi,hI⟩ | ⟨hi,hI⟩ | ⟨hi,hI⟩ | ⟨hi,hI⟩ | ⟨hi,hI⟩
  all_goals rcases profileLabel_cases m j with ⟨hj,hJ⟩ | ⟨hj,hJ⟩ | ⟨hj,hJ⟩ | ⟨hj,hJ⟩ | ⟨hj,hJ⟩
  all_goals rw [hi,hj]
  all_goals norm_num
  all_goals dsimp [profileOffset] at *
  all_goals omega

theorem profileLabel_fiber (m : Fin 5 → ℕ) (i : Fin 5) :
    ((Finset.range (∑ j, m j)).filter (fun k => profileLabel m k = i)) =
      Finset.Ico (profileOffset m i.castSucc) (profileOffset m i.succ) := by
  rw [profile_total]
  fin_cases i <;> ext k <;> simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  all_goals rcases profileLabel_cases m k with ⟨he,hk⟩ | ⟨he,hk⟩ | ⟨he,hk⟩ | ⟨he,hk⟩ | ⟨he,hk⟩
  all_goals rw [he]
  all_goals norm_num
  all_goals dsimp [profileOffset] at *
  all_goals omega

theorem profileLabel_fiber_card (m : Fin 5 → ℕ) (i : Fin 5) :
    ((Finset.range (∑ j, m j)).filter (fun k => profileLabel m k = i)).card = m i := by
  rw [profileLabel_fiber, Nat.card_Ico]
  fin_cases i <;> dsimp [profileOffset] <;> omega

theorem expandedProfileNode_multiplicity (z : Fin 5 → ℝ) (m : Fin 5 → ℕ)
    (hz : Function.Injective z) (i : Fin 5) :
    priorMultiplicity (expandedProfileNode z m) (∑ j, m j) (z i) = m i := by
  classical
  simp only [priorMultiplicity, expandedProfileNode, hz.eq_iff]
  exact profileLabel_fiber_card m i

theorem expandedProfileNode_grouped (z : Fin 5 → ℝ) (m : Fin 5 → ℕ)
    (hz : Function.Injective z) : GroupedPrefix (expandedProfileNode z m) (∑ i, m i) := by
  intro start k hk he j hj
  have hl : profileLabel m (start+k) = profileLabel m start := hz he
  have h₁ := profileLabel_monotone m (show start ≤ start+j by omega)
  have h₂ := profileLabel_monotone m (show start+j ≤ start+k by omega)
  have hmid : profileLabel m (start+j) = profileLabel m start :=
    le_antisymm (hl ▸ h₂) h₁
  exact congrArg z hmid

theorem profileHermite_degree (z : Fin 5 → ℝ) (m : Fin 5 → ℕ) (J : ℕ → ℝ → ℝ) :
    (profileHermite z m J).degree < (∑ i, m i) :=
  (newton_hermite_stage_invariant (expandedProfileNode z m) J (∑ i, m i)).1

theorem profileHermite_jets (z : Fin 5 → ℝ) (m : Fin 5 → ℕ) (J : ℕ → ℝ → ℝ)
    (hz : Function.Injective z) (i : Fin 5) (j : ℕ) (hj : j < m i) :
    polynomialJets (profileHermite z m J) j (z i) = J j (z i) := by
  apply (newton_hermite_stage_invariant (expandedProfileNode z m) J (∑ i, m i)).2
  rw [expandedProfileNode_multiplicity z m hz i]
  exact hj

theorem profileHermite_unique (z : Fin 5 → ℝ) (m : Fin 5 → ℕ) (J : ℕ → ℝ → ℝ)
    (hz : Function.Injective z) (P : Polynomial ℝ) (hP : P.degree < (∑ i, m i))
    (hj : ∀ i j, j < m i → polynomialJets P j (z i) = J j (z i)) :
    P = profileHermite z m J := by
  apply newton_hermite_unique 5 z m P (profileHermite z m J) hz hP (profileHermite_degree z m J)
  intro i j hji
  exact (hj i j hji).trans (profileHermite_jets z m J hz i j hji).symm

def HermiteConstructorContract : Prop :=
  ∀ (z : Fin 5 → ℝ) (m : Fin 5 → ℕ) (J : ℕ → ℝ → ℝ), Function.Injective z →
    (profileHermite z m J).degree < (∑ i, m i) ∧
    (∀ i j, j < m i → polynomialJets (profileHermite z m J) j (z i) = J j (z i)) ∧
    (∀ P : Polynomial ℝ, P.degree < (∑ i, m i) →
      (∀ i j, j < m i → polynomialJets P j (z i) = J j (z i)) → P = profileHermite z m J) ∧
    sourceNewtonPolynomial (expandedProfileNode z m) J (∑ i, m i) = profileHermite z m J ∧
    sourceNewtonHorner (expandedProfileNode z m)
      (fun i => confluentTable (expandedProfileNode z m) J i 0) (∑ i, m i) 0 = profileHermite z m J

theorem hermite_constructor : HermiteConstructorContract := by
  intro z m J hz
  exact ⟨profileHermite_degree z m J, profileHermite_jets z m J hz,
    profileHermite_unique z m J hz,
    newton_hermite_confluent_bridge (expandedProfileNode z m) J (∑ i, m i)
      (expandedProfileNode_grouped z m hz)⟩

theorem profileHermite_permute (z : Fin 5 → ℝ) (m : Fin 5 → ℕ) (J : ℕ → ℝ → ℝ)
    (hz : Function.Injective z) (e : Equiv.Perm (Fin 5)) :
    profileHermite (z ∘ e) (m ∘ e) J = profileHermite z m J := by
  have hsum : (∑ i, m (e i)) = ∑ i, m i := Equiv.sum_comp e m
  apply profileHermite_unique z m J hz
  · simpa only [Function.comp_apply, hsum] using profileHermite_degree (z ∘ e) (m ∘ e) J
  · intro i j hj
    have h := profileHermite_jets (z ∘ e) (m ∘ e) J (hz.comp e.injective) (e.symm i) j
      (by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hj)
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using h

theorem canonicalNodes_strictMono (a : ℝ) (ha : physical a) : StrictMono (canonicalNodes a) := by
  obtain ⟨h₀,h₁,h₂,h₃,h₄,h₅,_⟩ := contact_order_ordered_contacts a ha
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [canonicalNodes] at * <;> linarith

theorem canonicalNodes_bounds (a : ℝ) (ha : physical a) (i : Fin 5) :
    -1 ≤ canonicalNodes a i ∧ canonicalNodes a i < 1 := by
  obtain ⟨h₀,h₁,h₂,h₃,h₄,h₅,_⟩ := contact_order_ordered_contacts a ha
  fin_cases i <;> norm_num [canonicalNodes] <;> constructor <;> linarith

def hermitePolynomial (s a : ℝ) (m : Fin 5 → ℕ) : Polynomial ℝ :=
  profileHermite (canonicalNodes a) m (potentialJet s)

theorem hermitePolynomial_degree (s a : ℝ) (m : Fin 5 → ℕ) :
    (hermitePolynomial s a m).degree < (∑ i, m i) := profileHermite_degree _ _ _

theorem hermitePolynomial_jets (s a : ℝ) (m : Fin 5 → ℕ) (ha : physical a)
    (i : Fin 5) (j : ℕ) (hj : j < m i) :
    polynomialJets (hermitePolynomial s a m) j (canonicalNodes a i) =
      potentialJet s j (canonicalNodes a i) :=
  profileHermite_jets _ _ _ (canonicalNodes_strictMono a ha).injective i j hj

theorem hermitePolynomial_source_order (s a : ℝ) (m : Fin 5 → ℕ) (ha : physical a) :
    profileHermite (sourceNodes a) (m ∘ sourceNodeOrder) (potentialJet s) =
      hermitePolynomial s a m := by
  rw [sourceNodes_eq_canonical]
  exact profileHermite_permute _ _ _ (canonicalNodes_strictMono a ha).injective sourceNodeOrder

#print axioms profileHermite_permute
#print axioms canonicalNodes_strictMono
#print axioms canonicalNodes_bounds
#print axioms hermitePolynomial_jets
#print axioms hermitePolynomial_source_order
#check hermite_constructor
#print axioms hermite_constructor
end Blueprint.Thomson.Finite
