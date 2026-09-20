import Thomson8.Data
import Thomson8.MinorantData
import Thomson8.Derivative
import Thomson8.Quartic
import Thomson8.MatrixBounds

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Thomson8

def quarticK (c0 c1 c2 c3 c4 x : K) : K :=
  K.add c0 (K.mul x (K.add c1 (K.mul x (K.add c2 (K.mul x (K.add c3 (K.mul x c4)))))))

theorem eval_quarticK (c0 c1 c2 c3 c4 x : K) :
    (quarticK c0 c1 c2 c3 c4 x).eval =
      quartic c0.eval c1.eval c2.eval c3.eval c4.eval x.eval := by
  simp [quarticK,quartic]

def qCoeff (j ell : ℕ) : K := (Data.minorantQuartic.getD j []).getD ell K.zero

def qAt (ell : ℕ) (x : K) : K :=
  quarticK (qCoeff 0 ell) (qCoeff 1 ell) (qCoeff 2 ell) (qCoeff 3 ell) (qCoeff 4 ell) x

noncomputable def qRealCoeff (j : ℕ) : ℝ :=
  ∑ ell : Fin 5, logValues ell * (qCoeff j ell).eval

noncomputable def minorantQ (x : ℝ) : ℝ :=
  quartic (qRealCoeff 0) (qRealCoeff 1) (qRealCoeff 2) (qRealCoeff 3) (qRealCoeff 4) x

theorem minorantQ_at (x : K) :
    minorantQ x.eval = ∑ ell : Fin 5, logValues ell * (qAt ell x).eval := by
  simp only [minorantQ,qRealCoeff,qAt,eval_quarticK,quartic,Fin.sum_univ_succ,
    Fin.val_zero,Fin.val_succ,Finset.univ_eq_empty,Finset.sum_empty]
  ring

def qBox (x : K) : Box := Box.sumFin 5 fun ell =>
  Box.times (cachedLogs ell) (encloseK (qAt ell x))

theorem qBox_contains (x : K) : (qBox x).Contains (minorantQ x.eval) := by
  rw [minorantQ_at]
  exact Box.contains_sumFin 5 _ _ fun ell =>
    Box.contains_times (cachedLogs_contains ell) (encloseK_contains _)

def qLeadingBox : Box := Box.sumFin 5 fun ell =>
  Box.times (cachedLogs ell) (encloseK (qCoeff 4 ell))

theorem qLeadingBox_contains : qLeadingBox.Contains (qRealCoeff 4) :=
  Box.contains_sumFin 5 _ _ fun ell =>
    Box.contains_times (cachedLogs_contains ell) (encloseK_contains _)

theorem minorantQ_leading_pos : 0 < qRealCoeff 4 := by
  have h : (0 : ℚ) < qLeadingBox.lo := by decide +kernel
  exact (Rat.cast_pos.mpr h).trans_le qLeadingBox_contains.1

theorem minorantQ_minus_one_pos : 0 < minorantQ (-1) := by
  have h : (0 : ℚ) < (qBox (K.ofRat (-1))).lo := by decide +kernel
  have hc := qBox_contains (K.ofRat (-1))
  simpa using (Rat.cast_pos.mpr h).trans_le hc.1

theorem minorantQ_D_neg : minorantQ nodeD.eval < 0 := by
  have h : (qBox nodeD).hi < (0 : ℚ) := by decide +kernel
  exact (qBox_contains nodeD).2.trans_lt (by exact_mod_cast h)

theorem minorantQ_B_pos : 0 < minorantQ nodeB.eval := by
  have h : (0 : ℚ) < (qBox nodeB).lo := by decide +kernel
  exact (Rat.cast_pos.mpr h).trans_le (qBox_contains nodeB).1

theorem minorantQ_C_neg : minorantQ nodeC.eval < 0 := by
  have h : (qBox nodeC).hi < (0 : ℚ) := by decide +kernel
  exact (qBox_contains nodeC).2.trans_lt (by exact_mod_cast h)

theorem minorantQ_A_pos : 0 < minorantQ nodeA.eval := by
  have h : (0 : ℚ) < (qBox nodeA).lo := by decide +kernel
  exact (Rat.cast_pos.mpr h).trans_le (qBox_contains nodeA).1

def linearFactor (c : K) : Poly :=
  Poly.add (Poly.const (K.neg c)) (Poly.monomial ⟨1,0,0⟩)

def contactFactor : Poly :=
  Poly.mul (Poly.pow (linearFactor (K.ofRat (-1))) 4)
    (Poly.mul (linearFactor nodeA) (Poly.mul (linearFactor nodeB)
      (Poly.mul (linearFactor nodeC) (linearFactor nodeD))))

def qComponent (ell : ℕ) : Poly :=
  (List.range 5).map fun j => (⟨j,0,0⟩,qCoeff j ell)

def derivativeNumerator (ell : ℕ) : Poly :=
  Poly.add (Poly.const (K.ofRat (if ell=0 then 1 else 0)))
    (Poly.scale (K.ofRat 2) (Poly.mul (linearFactor K.one)
      (Poly.normalize (Poly.derivU (hermiteComponent Data.hermite ell)))))

theorem derivative_factor_check (ell : Fin 5) :
    (Poly.add (derivativeNumerator ell)
      (Poly.scale (K.ofRat (-1)) (Poly.mul contactFactor (qComponent ell)))).isZero := by
  fin_cases ell <;> decide +kernel

theorem derivative_factor_component (ell : Fin 5) (x : ℝ) :
    (derivativeNumerator ell).eval x 0 0 =
      (contactFactor).eval x 0 0 * (qComponent ell).eval x 0 0 := by
  simpa only [Poly.eval_mul] using
    Poly.eval_eq_of_check _ _ (derivative_factor_check ell) x 0 0

#print axioms minorantQ_A_pos
#print axioms derivative_factor_component

end Thomson8
