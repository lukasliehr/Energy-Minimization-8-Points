import AllS.Units.N_AI.N_fixed_tables.LinearSupport

noncomputable section
namespace Blueprint.CAP

/-- A closed rational-polynomial identity can be kernel checked once, then
    evaluated without elaborating a large real `ring` normalization proof. -/
theorem evalRationalList_mul3 (q d e v : List ℚ)
    (h : listPolynomial q=listPolynomial d*listPolynomial e*listPolynomial v)
    (a : ℝ) : evalRationalList q a=
      evalRationalList d a*evalRationalList e a*evalRationalList v a := by
  have he := congrArg (Polynomial.eval₂RingHom (Rat.castHom ℝ) a) h
  simpa only [map_mul,Polynomial.coe_eval₂RingHom,evalRationalList_eq] using he

theorem evalIntegerList_rat (p : List ℤ) (a : ℝ) :
    evalIntegerList p a=evalRationalList (p.map Int.cast) a := by
  induction p with
  | nil => simp [evalIntegerList,evalRationalList,listPolynomial_nil]
  | cons c p ih =>
    simp only [evalIntegerList,listPolynomial_cons,Polynomial.eval₂_add,
      Polynomial.eval₂_C,Polynomial.eval₂_mul,Polynomial.eval₂_X] at ih ⊢
    simp only [List.map_cons,evalRationalList]
    rw [← ih]
    simp

theorem evalClearedIntegerIdentity (A : List ℤ) (p v : List ℚ) (lam scale : ℤ)
    (h : Polynomial.C (lam:ℚ)*listPolynomial (A.map Int.cast)=
      Polynomial.C (scale:ℚ)*listPolynomial p*listPolynomial v)
    (a : ℝ) : (lam:ℝ)*evalIntegerList A a=
      (scale:ℝ)*evalRationalList p a*evalRationalList v a := by
  have he := congrArg (Polynomial.eval₂RingHom (Rat.castHom ℝ) a) h
  simpa only [map_mul,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,
    map_intCast,Rat.cast_intCast,← evalRationalList_eq,← evalIntegerList_rat] using he

#print axioms evalClearedIntegerIdentity
end Blueprint.CAP
