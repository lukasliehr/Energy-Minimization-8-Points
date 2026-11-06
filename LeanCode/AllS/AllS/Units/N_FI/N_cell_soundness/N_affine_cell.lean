import Blueprint.Cover
import Blueprint.CAPContracts
import AllS.Units.N_F.N_cell_soundness

noncomputable section
namespace Blueprint.Thomson.Finite

theorem eq_aS_of_stationary_root (s a : ℝ) (hs : 0 ≤ s)
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hF : F s a = 0) : a = aS s := by
  obtain ⟨b, hb, huniq⟩ := Blueprint.stationary_root_unique s hs
  exact (huniq a ⟨ha, hF⟩).trans (huniq (aS s) (aS_mem_and_root s hs)).symm

/-- Transport the complete closed normalized interval to the specified cover
cell, including both endpoints and its unique stationary height. -/
theorem cellSpec_of_affine_minimizers (i : Fin 30) (c h : ℝ)
    (hh : 0 < h) (hlo : c - h = Blueprint.lower i)
    (hhi : c + h = Blueprint.upper i)
    (hmin : ∀ x ∈ CAP.cellDomain, IsUniqueMinimizer (c + h * x) (X (aS (c + h * x)))) :
    Blueprint.CellSpec i := by
  intro s hs hslo hshi a ha hF
  let x := (s - c) / h
  have hx : x ∈ CAP.cellDomain := by
    constructor
    · apply (le_div_iff₀ hh).2
      rw [← hlo] at hslo
      linarith
    · apply (div_le_iff₀ hh).2
      rw [← hhi] at hshi
      linarith
  have hex : c + h * x = s := by
    dsimp [x]
    field_simp [ne_of_gt hh]
    <;> ring
  have h := hmin x hx
  rw [hex] at h
  simpa only [eq_aS_of_stationary_root s a hs ha hF] using h

/-- Actual mathematical certificates on the normalized interval discharge the
exact cover-cell conclusion; computational receipts are not premises. -/
theorem cellSpec_of_affine_certificates (i : Fin 30) (c h : ℝ)
    (hh : 0 < h) (hlo : c - h = Blueprint.lower i)
    (hhi : c + h = Blueprint.upper i) (D : ℕ) (m : Fin 5 → ℕ)
    (hc : ∀ x ∈ CAP.cellDomain, Certificate (c + h * x) (aS (c + h * x)) D m) :
    Blueprint.CellSpec i :=
  cellSpec_of_affine_minimizers i c h hh hlo hhi
    (fun x hx => certificate_soundness _ _ D m (hc x hx))

#print axioms eq_aS_of_stationary_root
#print axioms cellSpec_of_affine_minimizers
#print axioms cellSpec_of_affine_certificates
end Blueprint.Thomson.Finite
