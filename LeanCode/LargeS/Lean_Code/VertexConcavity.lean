import Lean_Code.PackingGeometry

open Real
noncomputable section
namespace SquareAntiprismVerification

def vertexTent (ρ x : ℝ) : ℝ :=
  if x ≤ ρ then x / ρ else (1 - x) / (1 - ρ)

lemma vertexTent_sum_lower {ι : Type*} [Fintype ι] (x : ι → ℝ) (ρ : ℝ)
    (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1)
    (m : ℤ) (hsum : ∑ i, x i = (m : ℝ) + ρ) :
    1 ≤ ∑ i, vertexTent ρ (x i) := by
  classical
  let A : ℝ := ∑ i, if x i ≤ ρ then x i else 0
  let B : ℝ := ∑ i, if x i ≤ ρ then 0 else 1 - x i
  let N : ℤ := ∑ i, if x i ≤ ρ then 0 else 1
  have hN : (N : ℝ) = ∑ i, if x i ≤ ρ then (0 : ℝ) else 1 := by
    simp [N]
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i hi => by split_ifs <;> linarith [(hx i).1])
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i hi => by split_ifs <;> linarith [(hx i).2])
  have hsplit : (∑ i, x i) = (N : ℝ) + A - B := by
    rw [hN]
    dsimp [A, B]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> ring
  have htentsum : (∑ i, vertexTent ρ (x i)) = A / ρ + B / (1 - ρ) := by
    dsimp [A, B]
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    unfold vertexTent
    split_ifs <;> simp
  by_contra hn
  have hlt : A / ρ + B / (1 - ρ) < 1 := by rw [← htentsum]; exact lt_of_not_ge hn
  have hden : 0 < 1 - ρ := by linarith [hρ.2]
  have hAless : A < ρ := by
    have h := div_nonneg hB hden.le
    have hh : A / ρ < 1 := by linarith
    simpa using (div_lt_iff₀ hρ.1).mp hh
  have hBless : B < 1 - ρ := by
    have h := div_nonneg hA hρ.1.le
    have hh : B / (1 - ρ) < 1 := by linarith
    simpa using (div_lt_iff₀ hden).mp hh
  have hlow : (N : ℝ) - 1 < (m : ℝ) := by linarith
  have hhigh : (m : ℝ) < (N : ℝ) := by linarith
  have hi₁ : N - 1 < m := by exact_mod_cast hlow
  have hi₂ : m < N := by exact_mod_cast hhigh
  omega

lemma concave_vertexTent_lower (f : ℝ → ℝ) (ρ x : ℝ)
    (hf : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) f) (hfzero : f 0 = 0) (hfone : f 1 = 0)
    (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    vertexTent ρ x * f ρ ≤ f x := by
  have hρmem : ρ ∈ Set.Icc (0 : ℝ) 1 := ⟨hρ.1.le, hρ.2.le⟩
  by_cases hxρ : x ≤ ρ
  · have hw : 0 ≤ x / ρ := div_nonneg hx.1 hρ.1.le
    have hwle : x / ρ ≤ 1 := (div_le_one hρ.1).mpr hxρ
    have h := hf.2 (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1) hρmem
      (by linarith : 0 ≤ 1 - x / ρ) hw (by ring)
    have harg : (1 - x / ρ) * 0 + (x / ρ) * ρ = x := by
      field_simp [hρ.1.ne']
      ring
    simp only [smul_eq_mul] at h
    rw [harg] at h
    simpa only [hfzero, mul_zero, zero_add, vertexTent, if_pos hxρ] using h
  · have hden : 0 < 1 - ρ := by linarith [hρ.2]
    have hw : 0 ≤ (1 - x) / (1 - ρ) := div_nonneg (by linarith [hx.2]) hden.le
    have hwle : (1 - x) / (1 - ρ) ≤ 1 := (div_le_one hden).mpr (by linarith)
    have h := hf.2 hρmem (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1) hw
      (by linarith : 0 ≤ 1 - (1 - x) / (1 - ρ)) (by ring)
    have harg : (1 - x) / (1 - ρ) * ρ + (1 - (1 - x) / (1 - ρ)) * 1 = x := by
      field_simp
      ring
    simp only [smul_eq_mul] at h
    rw [harg] at h
    simpa only [hfone, mul_zero, add_zero, vertexTent, if_neg hxρ] using h

/-- The one-vertex concavity inequality after rescaling `[α,2α]` to
`[0,1]`.  The angle sum has a fixed nonintegral fractional part `ρ`. -/
theorem one_vertex_concavity_bound {ι : Type*} [Fintype ι]
    (f : ℝ → ℝ) (ρ : ℝ) (hf : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) f)
    (hfzero : f 0 = 0) (hfone : f 1 = 0) (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1)
    (hfρ : 0 ≤ f ρ) (x : ι → ℝ) (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1)
    (m : ℤ) (hsum : ∑ i, x i = (m : ℝ) + ρ) :
    f ρ ≤ ∑ i, f (x i) := by
  have hsumlower := vertexTent_sum_lower x ρ hρ hx m hsum
  have hsumf := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    concave_vertexTent_lower f ρ (x i) hf hfzero hfone hρ (hx i))
  rw [← Finset.sum_mul] at hsumf
  have h := mul_le_mul_of_nonneg_right hsumlower hfρ
  simpa only [one_mul] using h.trans hsumf

lemma strictConcave_vertexTent_lt (f : ℝ → ℝ) (ρ x : ℝ)
    (hf : StrictConcaveOn ℝ (Set.Icc (0 : ℝ) 1) f) (hfzero : f 0 = 0) (hfone : f 1 = 0)
    (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hxne : x ≠ ρ) :
    vertexTent ρ x * f ρ < f x := by
  have hρmem : ρ ∈ Set.Icc (0 : ℝ) 1 := ⟨hρ.1.le, hρ.2.le⟩
  by_cases hxρ : x ≤ ρ
  · have hw : 0 < x / ρ := div_pos hx.1 hρ.1
    have hwlt : x / ρ < 1 := (div_lt_one hρ.1).mpr (lt_of_le_of_ne hxρ hxne)
    have h := hf.2 (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1) hρmem hρ.1.ne
      (by linarith : 0 < 1 - x / ρ) hw (by ring)
    have harg : (1 - x / ρ) * 0 + (x / ρ) * ρ = x := by
      field_simp [hρ.1.ne']
      ring
    simp only [smul_eq_mul] at h
    rw [harg] at h
    simpa only [hfzero, mul_zero, zero_add, vertexTent, if_pos hxρ] using h
  · have hden : 0 < 1 - ρ := by linarith [hρ.2]
    have hw : 0 < (1 - x) / (1 - ρ) := div_pos (by linarith [hx.2]) hden
    have hwlt : (1 - x) / (1 - ρ) < 1 := (div_lt_one hden).mpr (by linarith)
    have h := hf.2 hρmem (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1) hρ.2.ne hw
      (by linarith : 0 < 1 - (1 - x) / (1 - ρ)) (by ring)
    have harg : (1 - x) / (1 - ρ) * ρ + (1 - (1 - x) / (1 - ρ)) * 1 = x := by
      field_simp
      ring
    simp only [smul_eq_mul] at h
    rw [harg] at h
    simpa only [hfone, mul_zero, add_zero, vertexTent, if_neg hxρ] using h

/-- If all rhombus angles are genuine interior angles, equality at a vertex
allows only one rhombus, at the distinguished angle. -/
theorem one_vertex_concavity_equality {ι : Type*} [Fintype ι]
    (f : ℝ → ℝ) (ρ : ℝ) (hf : StrictConcaveOn ℝ (Set.Icc (0 : ℝ) 1) f)
    (hfzero : f 0 = 0) (hfone : f 1 = 0) (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1)
    (hfρ : 0 < f ρ) (x : ι → ℝ) (hx : ∀ i, x i ∈ Set.Ioo (0 : ℝ) 1)
    (m : ℤ) (hsum : ∑ i, x i = (m : ℝ) + ρ) (heq : ∑ i, f (x i) = f ρ) :
    Fintype.card ι = 1 ∧ ∀ i, x i = ρ := by
  have hxclosed (i : ι) : x i ∈ Set.Icc (0 : ℝ) 1 := ⟨(hx i).1.le, (hx i).2.le⟩
  have htent := vertexTent_sum_lower x ρ hρ hxclosed m hsum
  have hall : ∀ i, x i = ρ := by
    intro i
    by_contra hne
    have hpoint (j : ι) (_ : j ∈ (Finset.univ : Finset ι)) :=
      concave_vertexTent_lower f ρ (x j) hf.concaveOn hfzero hfone hρ (hxclosed j)
    have hstrict := strictConcave_vertexTent_lt f ρ (x i) hf hfzero hfone hρ (hx i) hne
    have hsumlt := Finset.sum_lt_sum hpoint ⟨i, Finset.mem_univ _, hstrict⟩
    rw [← Finset.sum_mul, heq] at hsumlt
    have hmul := mul_le_mul_of_nonneg_right htent hfρ.le
    linarith
  have hcard : (Fintype.card ι : ℝ) * f ρ = f ρ := by
    simpa only [hall, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using heq
  have hc : (Fintype.card ι : ℝ) = 1 := by nlinarith
  exact ⟨by exact_mod_cast hc, hall⟩

end SquareAntiprismVerification
