import ThomsonNegative.Compact.Target.TableAssembly

noncomputable section
namespace ThomsonNegative.Compact.Target
open ThomsonNegative.Compact.Packed
variable {N S B W : ℕ}

theorem allOK_getD {L : List TM} (h : allOK L=true) (i : ℕ) (hi : i<L.length) :
    (L.getD i zeroTM).ok=true := by
  induction L generalizing i with
  | nil => simp at hi
  | cons T ts ih =>
    simp only [allOK,Bool.and_eq_true] at h
    cases i with
    | zero => exact h.1
    | succ i => exact ih h.2 i (by simpa using hi)

/-- Soundness of every coefficient of the executable H7 target constructor.
The semantic polynomial is explicit; its interior identification with the
geometric H7 is `semanticPolynomial_at_root` below. -/
theorem build_coefficients_sound (hg : Good N S B W) {Q P : TM} {q p : ℝ → ℝ}
    (hQ : Encl (mkCtx N S B W) Q q) (hP : Encl (mkCtx N S B W) P p)
    (hq : ∀ t ∈ Set.Icc (-1:ℝ) 1, q t ∈ Set.Icc (0:ℝ) 1)
    (ir2 : ℕ) (par : Parameters) (hok : (build (mkCtx N S B W) Q P ir2 par).ok=true) :
    (build (mkCtx N S B W) Q P ir2 par).coefficients.length=8 ∧
      ∀ i<8, Encl (mkCtx N S B W) ((build (mkCtx N S B W) Q P ir2 par).coefficients.getD i zeroTM)
        (fun t => (semanticPolynomial (q t) (extendedHeight q p t)).coeff i) := by
  obtain ⟨hS,hIR,hQok,hPok,hRok,htube,hJok,hCok⟩ := build_flags hok
  obtain ⟨hp,hR,he,hA⟩ := build_root_sound hg hQ hP hq ir2 par hok
  have hI : EOK (mkCtx N S B W) (ir2TM (mkCtx N S B W) ir2) (fun _ => (Real.sqrt 2)⁻¹) :=
    fun h => ir2TM_sound hg ir2 h
  have hT := hermiteCoefficients_eok hg hS par
    (build (mkCtx N S B W) Q P ir2 par).nodes (build (mkCtx N S B W) Q P ir2 par).jets
    q (extendedHeight q p) (extendedHeight_range q p hp)
    (sourceNodes_eok hg hI (EOK.of_encl hA))
    (fun i => ⟨EOK.of_encl (build_jets_sound hg hQ hP hq ir2 par hok i).1,
      EOK.of_encl (build_jets_sound hg hQ hP hq ir2 par hok i).2⟩)
  have hlen : (build (mkCtx N S B W) Q P ir2 par).coefficients.length=8 := hT.1
  refine ⟨hlen,fun i hi => ?_⟩
  exact hT.2 i hi (allOK_getD hCok i (by rw [hlen]; exact hi))

theorem semanticPolynomial_at_root (q p : ℝ → ℝ) (t : ℝ)
    (hq : q t ∈ Set.Ioo (0:ℝ) 1) :
    semanticPolynomial (q t) (extendedHeight q p t)=
      Geometry.hermiteH7 (q t) (sourceContact (aStar (2*q t-2))) := by
  rw [extendedHeight_interior q p t hq]
  exact semanticPolynomial_interior (q t) _ hq
    (aStar_negative_range (q t) ⟨hq.1,hq.2.le⟩)

/-- The public target interface, including the root and geometric H7 bridge.
Only the input packed enclosures, the closed cell parameter domain and one
Boolean kernel result are premises. -/
theorem build_sound (hg : Good N S B W) {Q P : TM} {q p : ℝ → ℝ}
    (hQ : Encl (mkCtx N S B W) Q q) (hP : Encl (mkCtx N S B W) P p)
    (hq : ∀ t ∈ Set.Icc (-1:ℝ) 1, q t ∈ Set.Icc (0:ℝ) 1)
    (ir2 : ℕ) (par : Parameters) (hok : (build (mkCtx N S B W) Q P ir2 par).ok=true) :
    Encl (mkCtx N S B W) (build (mkCtx N S B W) Q P ir2 par).height (extendedHeight q p) ∧
    (∀ t ∈ Set.Icc (-1:ℝ) 1, extendedHeight q p t ∈ Set.Ioo (5/16:ℝ) (1/3)) ∧
    (∀ i<8, Encl (mkCtx N S B W) ((build (mkCtx N S B W) Q P ir2 par).coefficients.getD i zeroTM)
      (fun t => (semanticPolynomial (q t) (extendedHeight q p t)).coeff i)) ∧
    (∀ t ∈ Set.Icc (-1:ℝ) 1, q t ∈ Set.Ioo (0:ℝ) 1 →
      extendedHeight q p t=aStar (2*q t-2) ∧
      semanticPolynomial (q t) (extendedHeight q p t)=
        Geometry.hermiteH7 (q t) (sourceContact (aStar (2*q t-2)))) := by
  obtain ⟨hp,hR,he,hA⟩ := build_root_sound hg hQ hP hq ir2 par hok
  exact ⟨hA,extendedHeight_range q p hp,
    (build_coefficients_sound hg hQ hP hq ir2 par hok).2,
    fun t ht hqt => ⟨extendedHeight_interior q p t hqt,semanticPolynomial_at_root q p t hqt⟩⟩

#print axioms build_coefficients_sound
#print axioms build_sound
end ThomsonNegative.Compact.Target
