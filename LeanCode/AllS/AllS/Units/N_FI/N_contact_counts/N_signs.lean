import AllS.Units.N_FI.N_contact_counts.N_null_vector

noncomputable section
open Real
namespace Blueprint.Thomson.Finite

theorem contactDenominator_entries (a : ℝ) :
    contactDenominator a 0=(contacts a 0-contacts a 1)*(contacts a 0-contacts a 2)*(contacts a 0-contacts a 3) ∧
    contactDenominator a 1=(contacts a 1-contacts a 0)*(contacts a 1-contacts a 2)*(contacts a 1-contacts a 3) ∧
    contactDenominator a 2=(contacts a 2-contacts a 0)*(contacts a 2-contacts a 1)*(contacts a 2-contacts a 3) ∧
    contactDenominator a 3=(contacts a 3-contacts a 0)*(contacts a 3-contacts a 1)*(contacts a 3-contacts a 2) := by
  have e0 : Finset.univ.erase (0:Fin 4)={1,2,3} := by decide
  have e1 : Finset.univ.erase (1:Fin 4)={0,2,3} := by decide
  have e2 : Finset.univ.erase (2:Fin 4)={0,1,3} := by decide
  have e3 : Finset.univ.erase (3:Fin 4)={0,1,2} := by decide
  simp only [contactDenominator,e0,e1,e2,e3]
  exact ⟨prod_three_fin4 _ _ _ _ (by decide) (by decide) (by decide),
    prod_three_fin4 _ _ _ _ (by decide) (by decide) (by decide),
    prod_three_fin4 _ _ _ _ (by decide) (by decide) (by decide),
    prod_three_fin4 _ _ _ _ (by decide) (by decide) (by decide)⟩

theorem contact_trace_bounds (a : ℝ) (ha : physical a) :
    contacts a 3 < a-1 ∧ a-1 < contacts a 1 := by
  have hb := packing_endpoint_bounds.1
  have ha0 : 1/4 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hr := Real.sqrt_nonneg (2:ℝ)
  have hrlo : 4/3 < √(2:ℝ) := by nlinarith
  have hn : √(2:ℝ) ≠ 0 := by positivity
  have hinv : (√(2:ℝ))⁻¹=√2/2 := by field_simp; nlinarith
  have hprod := mul_pos (sub_pos.mpr ha1) (sub_pos.mpr hrlo)
  change -a-(1-a)/√2 < a-1 ∧ a-1 < 2*a-1
  rw [div_eq_mul_inv,hinv]
  constructor <;> nlinarith

theorem contactNullVector_signs (a : ℝ) (ha : physical a) :
    0 < contactNullVector a 0 ∧ 0 < contactNullVector a 1 ∧
    contactNullVector a 2 < 0 ∧ 0 < contactNullVector a 3 := by
  obtain ⟨_,hDB,hB,hC,hCA,_,_,_⟩ := contact_order_ordered_contacts a ha
  obtain ⟨hDT,hTB⟩ := contact_trace_bounds a ha
  obtain ⟨h0,h1,h2,h3⟩ := contactDenominator_entries a
  have hAB : 0 < contacts a 0-contacts a 1 := by linarith
  have hAC : 0 < contacts a 0-contacts a 2 := by linarith
  have hAD : 0 < contacts a 0-contacts a 3 := by linarith
  have hBC : contacts a 1-contacts a 2 < 0 := by linarith
  have hBD : 0 < contacts a 1-contacts a 3 := by linarith
  have hCD : 0 < contacts a 2-contacts a 3 := by linarith
  have hBA : contacts a 1-contacts a 0 < 0 := by linarith
  have hCA' : contacts a 2-contacts a 0 < 0 := by linarith
  have hCB : 0 < contacts a 2-contacts a 1 := by linarith
  have hDA : contacts a 3-contacts a 0 < 0 := by linarith
  have hDB' : contacts a 3-contacts a 1 < 0 := by linarith
  have hDC : contacts a 3-contacts a 2 < 0 := by linarith
  dsimp only [contactNullVector]
  rw [h0,h1,h2,h3]
  exact ⟨div_pos (by linarith) (mul_pos (mul_pos hAB hAC) hAD),
    div_pos (by linarith) (mul_pos (mul_pos_of_neg_of_neg hBA hBC) hBD),
    div_neg_of_pos_of_neg (by linarith) (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hCA' hCB) hCD),
    div_pos_of_neg_of_neg (by linarith) (mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg hDA hDB') hDC)⟩

#print axioms contactNullVector_signs
end Blueprint.Thomson.Finite
