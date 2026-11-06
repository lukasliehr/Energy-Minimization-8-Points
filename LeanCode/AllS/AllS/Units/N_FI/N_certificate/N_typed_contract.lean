import AllS.Units.N_F.N_gram_map
import AllS.Units.N_F.N_newton_hermite

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

/-- The finite checker has exactly these four polynomial degrees. -/
def ActiveDegree (D : ℕ) : Prop := D=12 ∨ D=14 ∨ D=16 ∨ D=18

def ValidMomentPivots {d : ℕ} (p : MomentPivots d) : Prop :=
  ∀ k : Fin d,∃ j : Fin 11,momentPivotKey j=(k.val,(p k).val)

def univariateLift (i : Fin 3) (H : Polynomial ℝ) : Poly3 :=
  Polynomial.aeval (MvPolynomial.X i) H

def averagedPolynomial (H : Polynomial ℝ) : Poly3 :=
  MvPolynomial.C (1/3 : ℝ)*(univariateLift 0 H+univariateLift 1 H+univariateLift 2 H)

def centeredPolynomial (H : Polynomial ℝ) (energy : ℝ) : Poly3 :=
  averagedPolynomial H-MvPolynomial.C (energy/28)

def normalizedTarget (s a β : ℝ) (m : Fin 5 → ℕ) : Poly3 :=
  MvPolynomial.C β*centeredPolynomial (hermitePolynomial s a m) (Ehat s (X a))

/-- Mathematical certificate only: the source models and arithmetic receipts
are used to construct this proposition, never stored as trusted flags. -/
structure Certificate (s a : ℝ) (D : ℕ) (m : Fin 5 → ℕ) : Prop where
  s_nonneg : 0 ≤ s
  physical_a : physical a
  root : F s a=0
  degree_active : ActiveDegree D
  profile_valid : Profile.Valid D m
  witness : ∃ p : MomentPivots (D/2),∃ β : ℝ,∃ W : GramFamily (D/2),
    ValidMomentPivots p ∧ 0<β ∧ (∀ b,(W.val b).PosDef) ∧
      gramPoly a (D/2) p W=normalizedTarget s a β m

def CertificateTypedContract : Prop :=
  (∀ D,ActiveDegree D → 6≤D/2 ∧ D/2≤9 ∧ 2*(D/2)=D) ∧
  (∀ M : Matrix (Fin 0) (Fin 0) ℝ,M.PosDef) ∧
  (∀ s a D m,Certificate s a D m → 0 ≤ s ∧ physical a ∧ F s a=0 ∧
    Profile.Valid D m ∧ ∃ p : MomentPivots (D/2),∃ β : ℝ,∃ W : GramFamily (D/2),
      ValidMomentPivots p ∧ 0<β ∧ (∀ b,(W.val b).PosDef) ∧
      gramPoly a (D/2) p W=normalizedTarget s a β m)

theorem activeDegree_half {D : ℕ} (h : ActiveDegree D) : 6≤D/2 ∧ D/2≤9 ∧ 2*(D/2)=D := by
  rcases h with rfl | rfl | rfl | rfl <;> norm_num

theorem empty_matrix_posDef (M : Matrix (Fin 0) (Fin 0) ℝ) : M.PosDef := by
  constructor
  · ext i
    exact Fin.elim0 i
  · intro v hv
    exact False.elim (hv (Subsingleton.elim _ _))

theorem certificate_typed_contract : CertificateTypedContract := by
  refine ⟨fun D => activeDegree_half,empty_matrix_posDef,?_⟩
  intro s a D m h
  exact ⟨h.s_nonneg,h.physical_a,h.root,h.profile_valid,h.witness⟩

#check certificate_typed_contract
#print axioms certificate_typed_contract
end Blueprint.Thomson.Finite
