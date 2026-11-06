import Mathlib

/-!
# Strictness only on the moment directions used by equality

Nonnegativity of all certificate blocks is sufficient for the energy bound.
To extract selected vanishing moments, the distinguished block needs a positive
floor only on those coordinates. In the canonical F0 basis with pivot zero,
the first and third vertex moments are coordinates 0 and 2.
-/
noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Reduction

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def quadratic {n : ℕ} (W : Mat n) (v : Fin n → ℝ) : ℝ :=
  dotProduct v (W.mulVec v)

def selectedFloor {n : ℕ} (S : Finset (Fin n)) (δ : ℝ) : Mat n :=
  Matrix.diagonal (fun i => if i ∈ S then δ else 0)

lemma selectedFloor_psd {n : ℕ} (S : Finset (Fin n)) (δ : ℝ) (hδ : 0 ≤ δ) :
    (selectedFloor S δ).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  dsimp
  split_ifs <;> positivity

lemma quadratic_selectedFloor {n : ℕ} (S : Finset (Fin n)) (δ : ℝ) (v : Fin n → ℝ) :
    quadratic (selectedFloor S δ) v = δ * ∑ i ∈ S, (v i)^2 := by
  classical
  simp only [quadratic, selectedFloor, Matrix.mulVec_diagonal, dotProduct]
  simp [Finset.mul_sum, mul_ite, ite_mul, pow_two, mul_assoc, mul_comm, mul_left_comm]

lemma quadratic_sub {n : ℕ} (W M : Mat n) (v : Fin n → ℝ) :
    quadratic (W-M) v = quadratic W v-quadratic M v := by
  simp [quadratic,Matrix.sub_mulVec,dotProduct_sub]

lemma psd_of_selectedFloor {n : ℕ} (W : Mat n) (S : Finset (Fin n)) (δ : ℝ)
    (hδ : 0 ≤ δ) (hfloor : (W-selectedFloor S δ).PosSemidef) : W.PosSemidef := by
  have h := hfloor.add (selectedFloor_psd S δ hδ)
  simpa only [sub_add_cancel] using h

/-- A floor on selected coordinates suffices; full positive definiteness is unnecessary. -/
theorem selected_zero_of_floor {n : ℕ} (W : Mat n) (S : Finset (Fin n)) (δ : ℝ)
    (hδ : 0 < δ) (hfloor : (W-selectedFloor S δ).PosSemidef)
    (v : Fin n → ℝ) (hz : quadratic W v=0) : ∀ r ∈ S, v r=0 := by
  have hn : 0 ≤ quadratic (W-selectedFloor S δ) v := by
    simpa only [quadratic,star_trivial] using hfloor.dotProduct_mulVec_nonneg v
  rw [quadratic_sub,quadratic_selectedFloor,hz] at hn
  have hs : 0 ≤ ∑ i ∈ S, (v i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have he : ∑ i ∈ S, (v i)^2=0 := by nlinarith
  intro r hr
  exact sq_eq_zero_iff.mp ((Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (v i))).mp he r hr)

/-- Extraction from a positive sum of per-vertex quadratic forms. -/
theorem selected_moments_zero {n m : ℕ} (W : Mat n) (S : Finset (Fin n)) (δ : ℝ)
    (hδ : 0 < δ) (hfloor : (W-selectedFloor S δ).PosSemidef)
    (v : Fin m → Fin n → ℝ) (hz : ∑ j, quadratic W (v j)=0) :
    ∀ j, ∀ r ∈ S, v j r=0 := by
  have hW := psd_of_selectedFloor W S δ hδ.le hfloor
  have hn (j : Fin m) : 0 ≤ quadratic W (v j) := by
    simpa only [quadratic,star_trivial] using hW.dotProduct_mulVec_nonneg (v j)
  intro j
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hn i)).mp hz j (Finset.mem_univ _)
  exact selected_zero_of_floor W S δ hδ hfloor (v j) hj

/-- Specifically, only two of the six canonical F0 directions need a strict floor. -/
theorem first_third_moments_zero (W : Mat 6) (δ : ℝ) (hδ : 0 < δ)
    (hfloor : (W-selectedFloor ({0,2} : Finset (Fin 6)) δ).PosSemidef)
    (v : Fin 8 → Fin 6 → ℝ) (hz : ∑ j, quadratic W (v j)=0) :
    ∀ j, v j 0=0 ∧ v j 2=0 := by
  intro j
  have h := selected_moments_zero W ({0,2} : Finset (Fin 6)) δ hδ hfloor v hz j
  exact ⟨h 0 (by simp),h 2 (by simp)⟩

/-- Arbitrary rectangular square factors are semidefinite without any inverse test. -/
theorem factor_gram_psd {n r : ℕ} (L : Matrix (Fin n) (Fin r) ℝ) :
    (L*L.transpose).PosSemidef := by
  have h := (Matrix.PosSemidef.one (n := Fin r) (R := ℝ)).mul_mul_conjTranspose_same L
  simpa using h

/-- Positive scalar/Bernstein weights make every uncorrected block analytic. -/
theorem weighted_factor_gram_psd {n r k : ℕ} (w : Fin k → ℝ)
    (L : Fin k → Matrix (Fin n) (Fin r) ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i, w i • (L i*(L i).transpose)).PosSemidef := by
  exact Matrix.posSemidef_sum Finset.univ (fun i _ => (factor_gram_psd (L i)).smul (hw i))

#print axioms selected_zero_of_floor
#print axioms first_third_moments_zero
#print axioms weighted_factor_gram_psd
end ThomsonNegative.Reduction
