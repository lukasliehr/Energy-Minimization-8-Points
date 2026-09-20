import Thomson8.RootBounds
import Thomson8.LogInterval

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Thomson8

def logInput (i : ℕ) : K :=
  match i with
  | 0 => K.ofRat 2
  | 1 => K.add (K.ofRat 2) (K.scale (-2) nodeA)
  | 2 => K.add (K.ofRat 2) (K.scale (-2) nodeC)
  | _ => K.add (K.ofRat 2) (K.scale (-2) nodeD)

def logInputBox (i : ℕ) : Box := encloseK (logInput i)
def transformBox (i : ℕ) : Box :=
  Box.divide (Box.sub (logInputBox i) (Box.exact 1))
    (Box.add (logInputBox i) (Box.exact 1))

theorem logInput_positive (i : Fin 4) : 0 < (logInput i).eval := by
  have h : (0 : ℚ) < (logInputBox i).lo := by fin_cases i <;> decide +kernel
  exact (Rat.cast_pos.mpr h).trans_le (encloseK_contains (logInput i)).1

theorem transformBox_contains (i : Fin 4) :
    (transformBox i).Contains (((logInput i).eval-1)/((logInput i).eval+1)) := by
  apply Box.contains_divide
  · fin_cases i <;> decide +kernel
  · simpa [logInputBox] using Box.contains_sub (encloseK_contains (logInput i)) (Box.exact_contains 1)
  · simpa [logInputBox] using Box.contains_add (encloseK_contains (logInput i)) (Box.exact_contains 1)

theorem transform_small (i : Fin 4) :
    |((logInput i).eval-1)/((logInput i).eval+1)| ≤ 3/5 := by
  have h := transformBox_contains i
  have hb : -(3/5 : ℚ) ≤ (transformBox i).lo ∧ (transformBox i).hi ≤ 3/5 := by
    fin_cases i <;> decide +kernel
  rw [abs_le]
  have hl : -(3/5 : ℝ) ≤ (transformBox i).lo := by
    simpa only [Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hb.1
  have hu : ((transformBox i).hi : ℝ) ≤ 3/5 := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hb.2
  exact ⟨hl.trans h.1,h.2.trans hu⟩

def logBox (i : ℕ) : Box := Box.round (Box.logOfTransform 64 (transformBox i))

theorem logBox_contains (i : Fin 4) : (logBox i).Contains (Real.log (logInput i).eval) := by
  have h := Box.contains_logOfTransform (transformBox_contains i) (transform_small i) 64
  have hp := logInput_positive i
  have heq : (1+((logInput i).eval-1)/((logInput i).eval+1))/
      (1-((logInput i).eval-1)/((logInput i).eval+1)) = (logInput i).eval := by
    have hxp : (logInput i).eval+1 ≠ 0 := by linarith
    field_simp
    ring
  rw [heq] at h
  exact Box.contains_round h

noncomputable def logValues (ell : ℕ) : ℝ :=
  if ell=0 then 1 else Real.log (logInput (ell-1)).eval

def logBoxes (ell : ℕ) : Box := if ell=0 then Box.exact 1 else logBox (ell-1)

theorem logBoxes_contains (ell : Fin 5) : (logBoxes ell).Contains (logValues ell) := by
  fin_cases ell
  · simp [logBoxes, logValues, Box.Contains, Box.exact]
  · exact logBox_contains ⟨0,by decide⟩
  · exact logBox_contains ⟨1,by decide⟩
  · exact logBox_contains ⟨2,by decide⟩
  · exact logBox_contains ⟨3,by decide⟩

#print axioms logBoxes_contains

end Thomson8
