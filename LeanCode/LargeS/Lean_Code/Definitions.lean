import Mathlib

set_option maxHeartbeats 400000

/-!
Definitions used by the independent verification development.  They mirror
the frozen definitions in `Showcase.lean`; the final bridge unfolds both
copies and checks that the types coincide definitionally.
-/

open Real

noncomputable section

namespace SquareAntiprismVerification

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

def unitSphere : Set ℝ³ := {x | ‖x‖ = 1}

local notation "𝕊²" => unitSphere

def IsConfiguration (Y : Fin 8 → ℝ³) : Prop :=
  (∀ i, Y i ∈ 𝕊²) ∧ Function.Injective Y

abbrev Configuration8 := {Y : Fin 8 → ℝ³ // IsConfiguration Y}

def E (s : ℝ) (Y : Fin 8 → ℝ³) : ℝ :=
  ∑ i : Fin 8, ∑ j : Fin 8 with i < j, ‖Y i - Y j‖ ^ (-s)

def ℰ (s : ℝ) : ℝ :=
  ⨅ Y : Configuration8, E s Y

def Congruent (Y Z : Fin 8 → ℝ³) : Prop :=
  ∃ (U : ℝ³ ≃ₗᵢ[ℝ] ℝ³) (f : Equiv.Perm (Fin 8)), ∀ i, Z i = U (Y (f i))

def r (a : ℝ) : ℝ := √(1 - a)

def h (a : ℝ) : ℝ := √a

def X (a : ℝ) : Fin 8 → ℝ³ :=
  Fin.append
    (fun j : Fin 4 => !₂[r a * cos (j * π / 2), r a * sin (j * π / 2), h a])
    (fun j : Fin 4 =>
      !₂[r a * cos (π / 4 + j * π / 2),
        r a * sin (π / 4 + j * π / 2), -h a])

def dA (a : ℝ) : ℝ := 2 * (1 - a)
def dB (a : ℝ) : ℝ := 4 * (1 - a)
def dC (a : ℝ) : ℝ := 2 - √2 + (2 + √2) * a
def dD (a : ℝ) : ℝ := 2 + √2 + (2 - √2) * a
def q (s : ℝ) : ℝ := 1 + s / 2

def F (s a : ℝ) : ℝ :=
  16 * dA a ^ (-q s) + 16 * dB a ^ (-q s)
    - 8 * (2 + √2) * dC a ^ (-q s) - 8 * (2 - √2) * dD a ^ (-q s)

def G (s a : ℝ) : ℝ :=
  8 * dA a ^ (-s / 2) + 4 * dB a ^ (-s / 2)
    + 8 * dC a ^ (-s / 2) + 8 * dD a ^ (-s / 2)

def aInf : ℝ := (2 * √2 - 1) / 7
def tau : ℝ := 2 * (1 - aInf)
def P : Fin 8 → ℝ³ := X aInf

lemma finEight_split (i : Fin 8) :
    (∃ j : Fin 4, i = Fin.castAdd 4 j) ∨ (∃ j : Fin 4, i = Fin.natAdd 4 j) := by
  refine Fin.addCases (motive := fun i : Fin (4 + 4) =>
    (∃ j : Fin 4, i = Fin.castAdd 4 j) ∨ (∃ j : Fin 4, i = Fin.natAdd 4 j)) ?_ ?_ i
  · exact fun j => Or.inl ⟨j, rfl⟩
  · exact fun j => Or.inr ⟨j, rfl⟩

theorem X_mem_unitSphere (a : ℝ) (ha : a ∈ Set.Ioo (0 : ℝ) 1) (i : Fin 8) :
    X a i ∈ unitSphere := by
  have hra : (√(1 - a)) ^ 2 = 1 - a := Real.sq_sqrt (by linarith [ha.2])
  have hha : (√a) ^ 2 = a := Real.sq_sqrt (le_of_lt ha.1)
  rcases finEight_split i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [X, Fin.append_left, unitSphere, Set.mem_setOf_eq, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_succ, r, h, Real.norm_eq_abs, hra, hha]
    calc
      _ = (√(1 - a)) ^ 2 *
          (cos ((j : ℕ) * π / 2) ^ 2 + sin ((j : ℕ) * π / 2) ^ 2) + a := by ring
      _ = (√(1 - a)) ^ 2 + a := by rw [Real.cos_sq_add_sin_sq]; ring
      _ = 1 := by rw [hra]; ring
  · rw [X, Fin.append_right, unitSphere, Set.mem_setOf_eq, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_succ, r, h, Real.norm_eq_abs, hra, hha]
    calc
      _ = (√(1 - a)) ^ 2 *
          (cos (π / 4 + (j : ℕ) * π / 2) ^ 2 +
            sin (π / 4 + (j : ℕ) * π / 2) ^ 2) + a := by ring
      _ = (√(1 - a)) ^ 2 + a := by rw [Real.cos_sq_add_sin_sq]; ring
      _ = 1 := by rw [hra]; ring

theorem X_injective (a : ℝ) (ha : a ∈ Set.Ioo (0 : ℝ) 1) : Function.Injective (X a) := by
  intro i j hij
  have hr : 0 < r a := by
    unfold r
    exact Real.sqrt_pos.2 (by linarith [ha.2])
  have htwo : (2 : ℝ) * π / 2 = π := by ring
  have hthree : (3 : ℝ) * π / 2 = π + π / 2 := by ring
  rcases finEight_split i with ⟨u, rfl⟩ | ⟨u, rfl⟩ <;>
    rcases finEight_split j with ⟨v, rfl⟩ | ⟨v, rfl⟩
  · simp only [X, Fin.append_left] at hij
    have hx := congrArg (fun x : ℝ³ => x.ofLp (0 : Fin 3)) hij
    have hy := congrArg (fun x : ℝ³ => x.ofLp (1 : Fin 3)) hij
    have huv : u = v := by
      apply Fin.eq_of_val_eq
      fin_cases u <;> fin_cases v <;>
        simp [Real.cos_add, Real.sin_add, htwo, hthree, hr.ne'] at hx hy ⊢ <;> nlinarith
    simpa [huv]
  · simp only [X, Fin.append_left, Fin.append_right] at hij
    have hz := congrArg (fun x : ℝ³ => x.ofLp (2 : Fin 3)) hij
    simp [h] at hz
    have hh : 0 < √a := Real.sqrt_pos.2 ha.1
    linarith
  · simp only [X, Fin.append_left, Fin.append_right] at hij
    have hz := congrArg (fun x : ℝ³ => x.ofLp (2 : Fin 3)) hij
    simp [h] at hz
    have hh : 0 < √a := Real.sqrt_pos.2 ha.1
    linarith
  · simp only [X, Fin.append_right] at hij
    have hx := congrArg (fun x : ℝ³ => x.ofLp (0 : Fin 3)) hij
    have hy := congrArg (fun x : ℝ³ => x.ofLp (1 : Fin 3)) hij
    have hs2p : 0 < √(2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
    have huv : u = v := by
      apply Fin.eq_of_val_eq
      fin_cases u <;> fin_cases v <;>
        simp [Real.cos_add, Real.sin_add, htwo, hthree, hr.ne'] at hx hy ⊢ <;> nlinarith
    simpa [huv]

theorem X_isConfiguration (a : ℝ) (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    IsConfiguration (X a) :=
  ⟨X_mem_unitSphere a ha, X_injective a ha⟩

lemma E_nonneg (s : ℝ) (Y : Fin 8 → ℝ³) : 0 ≤ E s Y := by
  unfold E
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Real.rpow_nonneg (norm_nonneg _) _

theorem minimalEnergy_eq_of_global (s a : ℝ) (hX : IsConfiguration (X a))
    (hmin : ∀ Y : Fin 8 → ℝ³, IsConfiguration Y → E s (X a) ≤ E s Y) :
    ℰ s = E s (X a) := by
  let candidate : Configuration8 := ⟨X a, hX⟩
  letI : Nonempty Configuration8 := ⟨candidate⟩
  have hb : BddBelow (Set.range (fun Y : Configuration8 => E s Y)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨Y, rfl⟩
    exact E_nonneg s Y
  have hlo : (⨅ Y : Configuration8, E s Y) ≤ E s candidate :=
    ciInf_le (f := fun Y : Configuration8 => E s Y) hb candidate
  have hhi : E s (X a) ≤ ⨅ Y : Configuration8, E s Y := by
    apply le_ciInf
    intro Y
    exact hmin Y Y.property
  exact le_antisymm (by simpa only [ℰ, candidate] using hlo) hhi

end SquareAntiprismVerification
