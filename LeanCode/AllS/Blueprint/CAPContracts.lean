import Mathlib

/-!
Concrete representations for the all-s CAP implementation. These definitions
and the elementary lemmas below do not prove any numerical certificate or
analytic operation soundness. In particular `Valid` is a proposition to prove,
not an axiom obtained by constructing a data record.
-/
noncomputable section
open scoped BigOperators

namespace Blueprint.CAP

structure Box where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq

namespace Box

def WellFormed (I : Box) : Prop := I.lo ≤ I.hi

def Contains (I : Box) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

def point (q : ℚ) : Box := ⟨q, q⟩

def AddGate (I J K : Box) : Prop := K.lo ≤ I.lo + J.lo ∧ I.hi + J.hi ≤ K.hi

def MulGate (I J K : Box) : Prop :=
  ∀ x ∈ ({I.lo, I.hi} : Finset ℚ), ∀ y ∈ ({J.lo, J.hi} : Finset ℚ),
    K.lo ≤ x * y ∧ x * y ≤ K.hi

def InvGate (I K : Box) : Prop :=
  (0 < I.lo ∨ I.hi < 0) ∧ K.lo ≤ 1 / I.hi ∧ 1 / I.lo ≤ K.hi

def SqrtGate (I K : Box) : Prop :=
  0 ≤ I.lo ∧ 0 ≤ K.lo ∧ K.lo ^ 2 ≤ I.lo ∧ I.hi ≤ K.hi ^ 2

theorem contains_point (q : ℚ) : (point q).Contains (q : ℝ) := ⟨le_rfl, le_rfl⟩

theorem eq_of_contains_point {q : ℚ} {x : ℝ} (h : (point q).Contains x) :
    x = (q : ℝ) := le_antisymm h.2 h.1

theorem contains_add {I J K : Box} {x y : ℝ}
    (hI : I.Contains x) (hJ : J.Contains y) (hgate : AddGate I J K) :
    K.Contains (x + y) := by
  have hlo : (K.lo : ℝ) ≤ (I.lo : ℝ) + (J.lo : ℝ) := by
    exact_mod_cast hgate.1
  have hhi : (I.hi : ℝ) + (J.hi : ℝ) ≤ (K.hi : ℝ) := by
    exact_mod_cast hgate.2
  exact ⟨hlo.trans (add_le_add hI.1 hJ.1), (add_le_add hI.2 hJ.2).trans hhi⟩

end Box

def cellDomain : Set ℝ := Set.Icc (-1) 1

def scalarEval {N : ℕ} (a : Fin (N + 1) → ℝ) (x : ℝ) : ℝ :=
  ∑ k, a k * x ^ k.val

structure TM (N : ℕ) where
  coeff : Fin (N + 1) → Box
  error : ℚ

namespace TM

def CoeffContains {N : ℕ} (M : TM N) (a : Fin (N + 1) → ℝ) : Prop :=
  ∀ k, (M.coeff k).Contains (a k)

def Valid {N : ℕ} (M : TM N) (f : ℝ → ℝ) : Prop :=
  0 ≤ M.error ∧ ∃ a : Fin (N + 1) → ℝ,
    M.CoeffContains a ∧ ∀ x ∈ cellDomain,
      |f x - scalarEval a x| ≤ (M.error : ℝ)

/-- A selected coefficient vector is shared by all cell coordinates and all
uses of this witness. In proofs, select it once before invoking operation
recurrences; do not select unrelated vectors at individual cell points. -/
structure Witness {N : ℕ} (M : TM N) (f : ℝ → ℝ) where
  coeff : Fin (N + 1) → ℝ
  coeff_mem : M.CoeffContains coeff
  error_nonneg : 0 ≤ M.error
  remainder : ∀ x ∈ cellDomain, |f x - scalarEval coeff x| ≤ (M.error : ℝ)

theorem valid_iff_nonempty_witness {N : ℕ} (M : TM N) (f : ℝ → ℝ) :
    M.Valid f ↔ Nonempty (M.Witness f) := by
  constructor
  · rintro ⟨he, a, ha, hr⟩
    exact ⟨⟨a, ha, he, hr⟩⟩
  · rintro ⟨w⟩
    exact ⟨w.error_nonneg, w.coeff, w.coeff_mem, w.remainder⟩

def pointPolynomial {N : ℕ} (a : Fin (N + 1) → ℚ) : TM N :=
  ⟨fun k => Box.point (a k), 0⟩

theorem pointPolynomial_valid {N : ℕ} (a : Fin (N + 1) → ℚ) :
    (pointPolynomial a).Valid (scalarEval fun k => (a k : ℝ)) := by
  refine ⟨le_rfl, (fun k => (a k : ℝ)), ?_, ?_⟩
  · exact fun k => Box.contains_point (a k)
  · intro x hx
    simp [pointPolynomial]

/-- The same lower bound applies to the polynomial, represented function,
and their connecting segments. Proving this is an explicit numeric gate. -/
def CommonPositiveHull {N : ℕ} (M : TM N) (I : Box) (μ : ℚ) : Prop :=
  0 < μ ∧ μ ≤ I.lo ∧ ∀ a : Fin (N + 1) → ℝ,
    M.CoeffContains a → ∀ x ∈ cellDomain, ∀ r : ℝ,
      |r| ≤ (M.error : ℝ) → I.Contains (scalarEval a x + r)

end TM

structure MatrixTM (N m n : ℕ) where
  coeff : Fin (N + 1) → Matrix (Fin m) (Fin n) Box
  error : Matrix (Fin m) (Fin n) ℚ

def matrixEval {N m n : ℕ}
    (a : Fin (N + 1) → Matrix (Fin m) (Fin n) ℝ) (x : ℝ) :
    Matrix (Fin m) (Fin n) ℝ := fun i j => ∑ k, a k i j * x ^ k.val

def MatrixTM.Valid {N m n : ℕ} (M : MatrixTM N m n)
    (f : ℝ → Matrix (Fin m) (Fin n) ℝ) : Prop :=
  (∀ i j, 0 ≤ M.error i j) ∧
  ∃ a : Fin (N + 1) → Matrix (Fin m) (Fin n) ℝ,
    (∀ k i j, (M.coeff k i j).Contains (a k i j)) ∧
    ∀ x ∈ cellDomain, ∀ i j,
      |f x i j - matrixEval a x i j| ≤ (M.error i j : ℝ)

def evalQPoly (p : Polynomial ℚ) (a : ℝ) : ℝ :=
  p.eval₂ (algebraMap ℚ ℝ) a

structure RatFun where
  rational : Polynomial ℚ
  irrational : Polynomial ℚ
  denominator : Polynomial ℚ

def RatFun.DefinedAt (f : RatFun) (a : ℝ) : Prop :=
  evalQPoly f.denominator a ≠ 0

def RatFun.eval (f : RatFun) (a : ℝ) : ℝ :=
  (evalQPoly f.rational a + Real.sqrt 2 * evalQPoly f.irrational a) /
    evalQPoly f.denominator a

def RatFun.zero : RatFun := ⟨0, 0, 1⟩

def RatFun.one : RatFun := ⟨1, 0, 1⟩

/-- Unreduced arithmetic is intentional: no gcd or cancellation oracle is
needed to represent a coefficient in the linkage plan. -/
def RatFun.add (f g : RatFun) : RatFun :=
  ⟨f.rational * g.denominator + g.rational * f.denominator,
   f.irrational * g.denominator + g.irrational * f.denominator,
   f.denominator * g.denominator⟩

def RatFun.mul (f g : RatFun) : RatFun :=
  ⟨f.rational * g.rational + 2 * f.irrational * g.irrational,
   f.rational * g.irrational + f.irrational * g.rational,
   f.denominator * g.denominator⟩

/-- A predecessor is in Fin j, so an acyclic plan cannot read a missing or
future value. No getD/default-zero operation is part of this representation. -/
inductive LinearStep (inputs prior : ℕ) where
  | input (i : Fin inputs)
  | zero
  | add (i j : Fin prior)
  | scale (c : RatFun) (i : Fin prior)

structure LinearPlan (n : ℕ) where
  length : ℕ
  step : (j : Fin length) → LinearStep n j.val
  output : Fin n → Fin length

def earlier {len : ℕ} (j : Fin len) (i : Fin j.val) : Fin len :=
  ⟨i.val, i.isLt.trans j.isLt⟩

def LinearPlan.Values {n : ℕ} (P : LinearPlan n) (a : ℝ)
    (input : Fin n → ℝ) (values : Fin P.length → ℝ) : Prop :=
  ∀ j, values j = match P.step j with
    | .input i => input i
    | .zero => 0
    | .add i k => values (earlier j i) + values (earlier j k)
    | .scale c i => c.eval a * values (earlier j i)

def LinearPlan.DefinedAt {n : ℕ} (P : LinearPlan n) (a : ℝ) : Prop :=
  ∀ j, match P.step j with
    | .scale c _ => c.DefinedAt a
    | _ => True

def LinearPlan.Outputs {n : ℕ} (P : LinearPlan n) (a : ℝ)
    (input output : Fin n → ℝ) : Prop :=
  P.DefinedAt a ∧ ∃ values, P.Values a input values ∧
    ∀ i, output i = values (P.output i)

def squaredEuclidean {n : ℕ} (v : Fin n → ℝ) : ℝ := ∑ i, (v i) ^ 2

def quadratic {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * M i j * v j

def QuadraticBound {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (γ : ℝ) : Prop :=
  0 ≤ γ ∧ ∀ v : Fin n → ℝ, |quadratic M v| ≤ γ * squaredEuclidean v

def FloorGate (δ θ γ : ℚ) : Prop :=
  0 < δ ∧ 0 ≤ γ ∧ γ < δ * (1 - θ)

/-- The complete residual gives a quotient bound without a small-residual
assumption. This is a genuine operation lemma; it is not a cell acceptance. -/
theorem scalar_models_quotient_residual (U V : ℝ → ℝ) (P : Polynomial ℝ)
    (μ R : ℝ) (hμ : 0 < μ)
    (hsep : ∀ x ∈ cellDomain, μ ≤ |V x|)
    (hres : ∀ x ∈ cellDomain, |U x - V x * P.eval x| ≤ R) :
    ∀ x ∈ cellDomain, |U x / V x - P.eval x| ≤ R / μ := by
  intro x hx
  have hV : V x ≠ 0 := by
    intro hz
    have hs := hsep x hx
    rw [hz, abs_zero] at hs
    exact (not_le_of_gt hμ) hs
  have hR : 0 ≤ R := (abs_nonneg _).trans (hres x hx)
  have hid : U x / V x - P.eval x = (U x - V x * P.eval x) / V x := by
    field_simp
  rw [hid, abs_div]
  exact (div_le_div_of_nonneg_right (hres x hx) (abs_nonneg _)).trans
    (div_le_div_of_nonneg_left hR hμ (hsep x hx))

#print axioms Box.contains_add
#print axioms TM.valid_iff_nonempty_witness
#print axioms TM.pointPolynomial_valid
#print axioms scalar_models_quotient_residual

end Blueprint.CAP
