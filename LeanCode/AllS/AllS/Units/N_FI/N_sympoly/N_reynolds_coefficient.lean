import AllS.Units.N_F.N_definitions

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

/-- The normalized average over all six coordinate permutations. -/
def reynolds : Poly3 →ₗ[ℝ] Poly3 :=
  (6 : ℝ)⁻¹ • ∑ σ : Equiv.Perm (Fin 3), (MvPolynomial.rename σ).toLinearMap

/-- Distinct exponent vectors in the coordinate-permutation orbit. -/
def exponentOrbit (α : Fin 3 →₀ ℕ) : Finset (Fin 3 →₀ ℕ) :=
  Finset.univ.image (fun σ : Equiv.Perm (Fin 3) => Finsupp.equivMapDomain σ α)

private theorem exponentOrbit_fiber_card (α β : Fin 3 →₀ ℕ) (hβ : β ∈ exponentOrbit α) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 3) => Finsupp.equivMapDomain σ α = β)).card =
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 3) => Finsupp.equivMapDomain σ α = α)).card := by
  obtain ⟨τ,_,rfl⟩ := Finset.mem_image.mp hβ
  symm
  apply Finset.card_bij (fun σ _ => σ.trans τ)
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    rw [Finsupp.equivMapDomain_trans,hσ]
  · intro σ hσ ρ hρ h
    apply Equiv.ext
    intro i
    exact τ.injective (congrArg (fun e : Equiv.Perm (Fin 3) => e i) h)
  · intro ρ hρ
    have hh : Finsupp.equivMapDomain (ρ.trans τ.symm) α = α := by
      rw [Finsupp.equivMapDomain_trans, (Finset.mem_filter.mp hρ).2]
      ext i
      simp [Finsupp.equivMapDomain_apply]
    refine ⟨ρ.trans τ.symm, by simpa using hh, ?_⟩
    ext i
    simp

theorem exponentOrbit_nonempty (α : Fin 3 →₀ ℕ) : (exponentOrbit α).Nonempty := by
  refine ⟨α, Finset.mem_image.mpr ⟨Equiv.refl _, Finset.mem_univ _, ?_⟩⟩
  exact Finsupp.equivMapDomain_refl α

theorem exponentOrbit_average (α : Fin 3 →₀ ℕ) (f : (Fin 3 →₀ ℕ) → ℝ) :
    (∑ σ : Equiv.Perm (Fin 3), f (Finsupp.equivMapDomain σ α)) / 6 =
      (∑ β ∈ exponentOrbit α, f β) / (exponentOrbit α).card := by
  let m := (Finset.univ.filter
    (fun σ : Equiv.Perm (Fin 3) => Finsupp.equivMapDomain σ α = α)).card
  have hcard : 6 = (exponentOrbit α).card * m := by
    have h := Finset.card_eq_sum_card_image
      (fun σ : Equiv.Perm (Fin 3) => Finsupp.equivMapDomain σ α) Finset.univ
    change (Finset.univ : Finset (Equiv.Perm (Fin 3))).card =
      ∑ β ∈ exponentOrbit α, _ at h
    have hsum : (∑ β ∈ exponentOrbit α,
        (Finset.univ.filter (fun σ : Equiv.Perm (Fin 3) => Finsupp.equivMapDomain σ α = β)).card) =
        (exponentOrbit α).card*m := by
      calc
        _ = ∑ _β ∈ exponentOrbit α, m := by
          apply Finset.sum_congr rfl
          intro β hβ
          exact exponentOrbit_fiber_card α β hβ
        _ = _ := by simp
    rw [hsum] at h
    norm_num [Fintype.card_perm] at h
    exact h
  have hsum : (∑ σ : Equiv.Perm (Fin 3), f (Finsupp.equivMapDomain σ α)) =
      (m : ℝ) * ∑ β ∈ exponentOrbit α, f β := by
    rw [← Finset.sum_fiberwise_of_maps_to (t := exponentOrbit α)
      (g := fun σ : Equiv.Perm (Fin 3) => Finsupp.equivMapDomain σ α)
      (fun σ (_ : σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin 3)))) =>
        Finset.mem_image.mpr ⟨σ,Finset.mem_univ _,rfl⟩)
      (fun σ : Equiv.Perm (Fin 3) => f (Finsupp.equivMapDomain σ α))]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro β hβ
    calc
      _ = ∑ _σ ∈ Finset.univ.filter
          (fun σ : Equiv.Perm (Fin 3) => Finsupp.equivMapDomain σ α = β), f β := by
        apply Finset.sum_congr rfl
        intro σ hσ
        rw [(Finset.mem_filter.mp hσ).2]
      _ = _ := by simp [exponentOrbit_fiber_card α β hβ, m]
  have hcardR : (6 : ℝ) = (exponentOrbit α).card * (m : ℝ) := by exact_mod_cast hcard
  have hm : (m : ℝ) ≠ 0 := by intro hm; rw [hm,mul_zero] at hcardR; norm_num at hcardR
  have ho : ((exponentOrbit α).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr (exponentOrbit_nonempty α)).ne'
  rw [hsum,hcardR]
  field_simp

theorem coeff_rename_equiv (p : Poly3) (α : Fin 3 →₀ ℕ) (σ : Equiv.Perm (Fin 3)) :
    (MvPolynomial.rename σ p).coeff α = p.coeff (Finsupp.equivMapDomain σ.symm α) := by
  have h := MvPolynomial.coeff_rename_mapDomain σ σ.injective p (Finsupp.equivMapDomain σ.symm α)
  have hh : (Finsupp.equivMapDomain σ.symm α).mapDomain σ = α := by
    rw [← Finsupp.equivMapDomain_eq_mapDomain]
    ext i
    simp [Finsupp.equivMapDomain_apply]
  rw [hh] at h
  exact h

theorem reynolds_coeff_perm_sum (p : Poly3) (α : Fin 3 →₀ ℕ) :
    (reynolds p).coeff α =
      (∑ σ : Equiv.Perm (Fin 3), p.coeff (Finsupp.equivMapDomain σ α))/6 := by
  have hsum : (∑ σ : Equiv.Perm (Fin 3), p.coeff (Finsupp.equivMapDomain σ.symm α)) =
      ∑ σ : Equiv.Perm (Fin 3), p.coeff (Finsupp.equivMapDomain σ α) := by
    let e : Equiv.Perm (Equiv.Perm (Fin 3)) :=
      ⟨Equiv.symm,Equiv.symm,Equiv.symm_symm,Equiv.symm_symm⟩
    exact Equiv.sum_comp e (fun σ => p.coeff (Finsupp.equivMapDomain σ α))
  simp only [reynolds,LinearMap.smul_apply,LinearMap.sum_apply,AlgHom.toLinearMap_apply,
    MvPolynomial.coeff_smul,MvPolynomial.coeff_sum,coeff_rename_equiv,smul_eq_mul]
  rw [hsum]
  ring

theorem sympoly_reynolds_coefficient (p : Poly3) (α : Fin 3 →₀ ℕ) :
    (reynolds p).coeff α = (∑ β ∈ exponentOrbit α, p.coeff β)/(exponentOrbit α).card := by
  rw [reynolds_coeff_perm_sum]
  exact exponentOrbit_average α p.coeff

/-- A symmetric polynomial's orbit-sum coordinate is its single monomial coefficient. -/
theorem exponentOrbit_coeff_of_symmetric (p : Poly3) (hp : p.IsSymmetric)
    (α β : Fin 3 →₀ ℕ) (hβ : β ∈ exponentOrbit α) : p.coeff β = p.coeff α := by
  obtain ⟨σ,_,rfl⟩ := Finset.mem_image.mp hβ
  rw [Finsupp.equivMapDomain_eq_mapDomain]
  rw [← MvPolynomial.coeff_rename_mapDomain σ σ.injective p α, hp σ]

theorem reynolds_of_symmetric (p : Poly3) (hp : p.IsSymmetric) : reynolds p = p := by
  ext α
  rw [sympoly_reynolds_coefficient]
  have hsum : (∑ β ∈ exponentOrbit α, p.coeff β) =
      ((exponentOrbit α).card : ℝ)*p.coeff α := by
    calc
      _ = ∑ _β ∈ exponentOrbit α, p.coeff α := by
        apply Finset.sum_congr rfl
        exact fun β hβ => exponentOrbit_coeff_of_symmetric p hp α β hβ
      _ = _ := by simp
  rw [hsum]
  have hn : ((exponentOrbit α).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr (exponentOrbit_nonempty α)).ne'
  field_simp

#check sympoly_reynolds_coefficient
#print axioms sympoly_reynolds_coefficient
#print axioms reynolds_of_symmetric
end Blueprint.Thomson.Finite
