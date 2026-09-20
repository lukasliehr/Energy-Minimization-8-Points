import Coulomb8.DyadicArithmetic
import Coulomb8.NodeBounds
import Thomson8.GramAlgebra

namespace Coulomb8

def gramDetBox (u v t : Dyadic) : Dyadic := (Dyadic.sub (Dyadic.sub (Dyadic.sub (Dyadic.add (Dyadic.integer 1) (Dyadic.mul (Dyadic.mul (Dyadic.mul (Dyadic.integer 2) u) v) t)) (Dyadic.mul u u)) (Dyadic.mul v v)) (Dyadic.mul t t))

theorem gramDetBox_contains {u : Dyadic} {xu : ℝ} (hu : u.Contains xu) {v : Dyadic} {xv : ℝ} (hv : v.Contains xv) {t : Dyadic} {xt : ℝ} (ht : t.Contains xt) :
    (gramDetBox u v t).Contains (Thomson8.gramDet3 xu xv xt) := by
  simpa [gramDetBox,Thomson8.gramResidual,Thomson8.gramDet3,pow_two] using (Dyadic.contains_sub (Dyadic.contains_sub (Dyadic.contains_sub (Dyadic.contains_add_exact (Dyadic.contains_integer 1) (Dyadic.contains_mul_exact (Dyadic.contains_mul_exact (Dyadic.contains_mul_exact (Dyadic.contains_integer 2) hu) hv) ht)) (Dyadic.contains_mul_exact hu hu)) (Dyadic.contains_mul_exact hv hv)) (Dyadic.contains_mul_exact ht ht))

def gramResidualBox (u v t r s w : Dyadic) : Dyadic := (Dyadic.sub (Dyadic.add (Dyadic.add (Dyadic.add (Dyadic.add (Dyadic.add (Dyadic.mul (Dyadic.sub (Dyadic.integer 1) (Dyadic.mul t t)) (Dyadic.mul r r)) (Dyadic.mul (Dyadic.sub (Dyadic.integer 1) (Dyadic.mul v v)) (Dyadic.mul s s))) (Dyadic.mul (Dyadic.sub (Dyadic.integer 1) (Dyadic.mul u u)) (Dyadic.mul w w))) (Dyadic.mul (Dyadic.mul (Dyadic.mul (Dyadic.integer 2) (Dyadic.sub (Dyadic.mul v t) u)) r) s)) (Dyadic.mul (Dyadic.mul (Dyadic.mul (Dyadic.integer 2) (Dyadic.sub (Dyadic.mul u t) v)) r) w)) (Dyadic.mul (Dyadic.mul (Dyadic.mul (Dyadic.integer 2) (Dyadic.sub (Dyadic.mul u v) t)) s) w)) (Dyadic.sub (Dyadic.sub (Dyadic.sub (Dyadic.add (Dyadic.integer 1) (Dyadic.mul (Dyadic.mul (Dyadic.mul (Dyadic.integer 2) u) v) t)) (Dyadic.mul u u)) (Dyadic.mul v v)) (Dyadic.mul t t)))

theorem gramResidualBox_contains {u : Dyadic} {xu : ℝ} (hu : u.Contains xu) {v : Dyadic} {xv : ℝ} (hv : v.Contains xv) {t : Dyadic} {xt : ℝ} (ht : t.Contains xt) {r : Dyadic} {xr : ℝ} (hr : r.Contains xr) {s : Dyadic} {xs : ℝ} (hs : s.Contains xs) {w : Dyadic} {xw : ℝ} (hw : w.Contains xw) :
    (gramResidualBox u v t r s w).Contains (Thomson8.gramResidual xu xv xt xr xs xw) := by
  simpa [gramResidualBox,Thomson8.gramResidual,Thomson8.gramDet3,pow_two] using (Dyadic.contains_sub (Dyadic.contains_add_exact (Dyadic.contains_add_exact (Dyadic.contains_add_exact (Dyadic.contains_add_exact (Dyadic.contains_add_exact (Dyadic.contains_mul_exact (Dyadic.contains_sub (Dyadic.contains_integer 1) (Dyadic.contains_mul_exact ht ht)) (Dyadic.contains_mul_exact hr hr)) (Dyadic.contains_mul_exact (Dyadic.contains_sub (Dyadic.contains_integer 1) (Dyadic.contains_mul_exact hv hv)) (Dyadic.contains_mul_exact hs hs))) (Dyadic.contains_mul_exact (Dyadic.contains_sub (Dyadic.contains_integer 1) (Dyadic.contains_mul_exact hu hu)) (Dyadic.contains_mul_exact hw hw))) (Dyadic.contains_mul_exact (Dyadic.contains_mul_exact (Dyadic.contains_mul_exact (Dyadic.contains_integer 2) (Dyadic.contains_sub (Dyadic.contains_mul_exact hv ht) hu)) hr) hs)) (Dyadic.contains_mul_exact (Dyadic.contains_mul_exact (Dyadic.contains_mul_exact (Dyadic.contains_integer 2) (Dyadic.contains_sub (Dyadic.contains_mul_exact hu ht) hv)) hr) hw)) (Dyadic.contains_mul_exact (Dyadic.contains_mul_exact (Dyadic.contains_mul_exact (Dyadic.contains_integer 2) (Dyadic.contains_sub (Dyadic.contains_mul_exact hu hv) ht)) hs) hw)) (Dyadic.contains_sub (Dyadic.contains_sub (Dyadic.contains_sub (Dyadic.contains_add_exact (Dyadic.contains_integer 1) (Dyadic.contains_mul_exact (Dyadic.contains_mul_exact (Dyadic.contains_mul_exact (Dyadic.contains_integer 2) hu) hv) ht)) (Dyadic.contains_mul_exact hu hu)) (Dyadic.contains_mul_exact hv hv)) (Dyadic.contains_mul_exact ht ht)))

def nodeDyadic : Fin 4 → Dyadic := ![⟨106879073530039017138168416880705077704,106879073530039017138168450908941769799⟩,⟨-126524219860860429187037773670358056048,-126524219860860429187037705613884671858⟩,⟨58161977977939271616606603688680311917,58161977977939271616606661778513920815⟩,⟨-271920125038017305892943529568160768318,-271920125038017305892943471478327159420⟩]

theorem nodeDyadic_contains (i : Fin 4) : (nodeDyadic i).Contains (nodes a i) := by
  apply Dyadic.contains_of_box (nodeBox_contains i)
  all_goals fin_cases i <;> decide +kernel

end Coulomb8
