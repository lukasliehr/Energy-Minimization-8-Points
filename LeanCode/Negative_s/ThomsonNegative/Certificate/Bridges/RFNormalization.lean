import ThomsonNegative.Certificate.RFSound
import ThomsonNegative.Structure.Rational

noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Compact.Packed

lemma factors_inverse_product (L : List PolyData) (u : ℝ) :
    (L.map (fun p => (p.eval u)⁻¹)).prod=((L.map (fun p => p.eval u)).prod)⁻¹ := by
  induction L with
  | nil => simp
  | cons p L ih => simp only [List.map_cons,List.prod_cons,ih,mul_inv_rev]; ring

lemma rf_eval_as_divide (r : RFData) (u : ℝ) :
    r.eval u=r.numerator.eval u*qval r.unitInverse/(r.factors.map (fun p => p.eval u)).prod := by
  rw [RFData.eval,factors_inverse_product]
  rfl

/-- A shared exact bridge from shifted/factored records to unshifted integer
rational functions. The nonzero condition is only on the constant scale;
there is no parameter-dependent denominator premise. -/
theorem translated_rf_of_scaled (r : RFData) (source : Structure.RF) (c d a anchor : ℝ)
    (hnum : r.numerator.eval (a-anchor)=c*Structure.Packed.evalZ source.numerator a)
    (hden : (r.factors.map (fun p => p.eval (a-anchor))).prod=d*Structure.Packed.evalZ source.denominator a)
    (hscale : c*qval r.unitInverse=d) (hd : d ≠ 0) :
    r.eval (a-anchor)=source.eval a := by
  rw [rf_eval_as_divide,hnum,hden]
  have he : c*Structure.Packed.evalZ source.numerator a*qval r.unitInverse=d*Structure.Packed.evalZ source.numerator a := by
    calc
      _ = (c*qval r.unitInverse)*Structure.Packed.evalZ source.numerator a := by ring
      _ = _ := by rw [hscale]
  rw [he,mul_div_mul_left _ _ hd]
  rfl

#print axioms translated_rf_of_scaled
end ThomsonNegative.Certificate.Bridges
