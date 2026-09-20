import Thomson8.LogConstants

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Thomson8

def cachedLog0 : Box := ⟨(235865763225513194659870294484317311205/340282366920938463463374607431768211456),(235865763225513393616017991043989379115/340282366920938463463374607431768211456)⟩

theorem cachedLog0_eq : logBox 0 = cachedLog0 := by decide +kernel
theorem cachedLog0_contains : cachedLog0.Contains (Real.log (logInput 0).eval) := by
  rw [← cachedLog0_eq]
  exact logBox_contains ⟨0,by decide⟩
#print axioms cachedLog0_contains

def cachedLog1 : Box := ⟨(105235428902714443514413995132432439787/340282366920938463463374607431768211456),(105235428902714642470561691692104507709/340282366920938463463374607431768211456)⟩

theorem cachedLog1_eq : logBox 1 = cachedLog1 := by decide +kernel
theorem cachedLog1_contains : cachedLog1.Contains (Real.log (logInput 1).eval) := by
  rw [← cachedLog1_eq]
  exact logBox_contains ⟨1,by decide⟩
#print axioms cachedLog1_contains

def cachedLog2 : Box := ⟨(175361897627479649908817415070331814289/340282366920938463463374607431768211456),(175361897627479848864965111630003882243/340282366920938463463374607431768211456)⟩

theorem cachedLog2_eq : logBox 2 = cachedLog2 := by decide +kernel
theorem cachedLog2_contains : cachedLog2.Contains (Real.log (logInput 2).eval) := by
  rw [← cachedLog2_eq]
  exact logBox_contains ⟨2,by decide⟩
#print axioms cachedLog2_contains

def cachedLog3 : Box := ⟨(435969720647919106207249234894112816560/340282366920938463463374607431768211456),(435969720647919305163396931453784884529/340282366920938463463374607431768211456)⟩

theorem cachedLog3_eq : logBox 3 = cachedLog3 := by decide +kernel
theorem cachedLog3_contains : cachedLog3.Contains (Real.log (logInput 3).eval) := by
  rw [← cachedLog3_eq]
  exact logBox_contains ⟨3,by decide⟩
#print axioms cachedLog3_contains

def cachedLogs (ell : ℕ) : Box :=
  match ell with
  | 0 => Box.exact 1
  | 1 => cachedLog0
  | 2 => cachedLog1
  | 3 => cachedLog2
  | _ => cachedLog3

theorem cachedLogs_contains (ell : Fin 5) :
    (cachedLogs ell).Contains (logValues ell) := by
  fin_cases ell
  · simp [cachedLogs, logValues, Box.Contains, Box.exact]
  · exact cachedLog0_contains
  · exact cachedLog1_contains
  · exact cachedLog2_contains
  · exact cachedLog3_contains

end Thomson8
