import Blueprint.RootBridge

/-! Fixed finite-proof representations. Enumeration, degree and analytic theorems
are separate work items. No theorem from the admitted root showcase is imported. -/
noncomputable section
open Real
open scoped BigOperators

namespace Blueprint.Thomson.Finite

abbrev Configuration := Fin 8 → Point
abbrev Poly3 := MvPolynomial (Fin 3) ℝ
abbrev Tag := ℕ × ℕ × ℕ

def aInf : ℝ := (2 * √2 - 1) / 7
def aS (s : ℝ) : ℝ := SquareAntiprismVerification.aStar s
def physical (a : ℝ) : Prop := aInf < a ∧ a < 1 / 3

/-- Contact order in the source: A, B, C, D. -/
def contacts (a : ℝ) : Fin 4 → ℝ :=
  ![a, 2 * a - 1, -a + (1 - a) / √2, -a - (1 - a) / √2]

/-- Entire normalization used at and near the logarithmic endpoint. -/
def phi (s t : ℝ) : ℝ :=
  if s = 0 then -(1 / 2 : ℝ) * log (2 - 2 * t)
  else ((2 - 2 * t) ^ (-s / 2) - 1) / s

def PairSum (f : Fin 8 → Fin 8 → ℝ) : ℝ :=
  ∑ i : Fin 8, ∑ j : Fin 8 with i < j, f i j

def DistinctSum (f : Fin 8 → Fin 8 → Fin 8 → ℝ) : ℝ :=
  ∑ i : Fin 8, ∑ j : Fin 8, ∑ k : Fin 8,
    if i ≠ j ∧ j ≠ k ∧ k ≠ i then f i j k else 0

def Ehat (s : ℝ) (Y : Configuration) : ℝ :=
  PairSum (fun i j => phi s (inner ℝ (Y i) (Y j)))

def tagWeight (t : Tag) : ℕ := t.1 + 2 * t.2.1 + 3 * t.2.2

/-- Mathematical index set; ordered export lists must prove their enumeration. -/
def InvariantTags (D : ℕ) : Finset Tag :=
  ((Finset.range (D + 1)).product
    ((Finset.range (D + 1)).product (Finset.range (D + 1)))).filter
      (fun t => tagWeight t ≤ D)

def RetainedTags (D : ℕ) : Finset Tag :=
  (InvariantTags D).erase (0, 0, 0) |>.erase (2, 0, 0)

def sigma : Poly3 := MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2
def e2 : Poly3 := MvPolynomial.X 0 * MvPolynomial.X 1 +
  MvPolynomial.X 0 * MvPolynomial.X 2 + MvPolynomial.X 1 * MvPolynomial.X 2
def e3 : Poly3 := MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2
def invariantMonomial (t : Tag) : Poly3 := sigma ^ t.1 * e2 ^ t.2.1 * e3 ^ t.2.2

@[simp] theorem phi_zero (t : ℝ) : phi 0 t = -(1 / 2 : ℝ) * log (2 - 2 * t) := by
  simp [phi]

theorem phi_of_ne_zero (s t : ℝ) (hs : s ≠ 0) :
    phi s t = ((2 - 2 * t) ^ (-s / 2) - 1) / s := by
  simp [phi, hs]

theorem aS_mem_and_root (s : ℝ) (hs : 0 ≤ s) :
    aS s ∈ Set.Ioo (0 : ℝ) 1 ∧ F s (aS s) = 0 :=
  SquareAntiprismVerification.aStar_spec s hs

theorem candidate_is_configuration (a : ℝ) (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    IsConfiguration (X a) := Blueprint.antiprism_is_configuration a ha

#print axioms phi_zero
#print axioms phi_of_ne_zero
#print axioms aS_mem_and_root
end Blueprint.Thomson.Finite
