import ThomsonNegative.Certificate.Correction.RowSound
import ThomsonNegative.Compact.Target.ScalarCells

noncomputable section
namespace ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open ThomsonNegative.Compact.Packed

/-- Shift the height argument without changing the global parameter domain. -/
theorem shiftedHeight_sound {A : TM} {a : ℝ → ℝ} (ha : Encl context A a)
    (hok : (refresh context (addC context true (83*2^376) 1 A)).ok=true) :
    Encl context (refresh context (addC context true (83*2^376) 1 A))
      (fun t => a t-83/256) := by
  have he : ((83*2^376:ℕ):ℝ)/(2:ℝ)^384=83/256 := by
    push_cast
    rw [show (384:ℕ)=376+8 from rfl,pow_add]
    rw [show (2:ℝ)^8=256 by norm_num,mul_comm ((2:ℝ)^376) 256]
    exact mul_div_mul_right (83:ℝ) 256 (pow_ne_zero 376 (by norm_num))
  have h := addC_sound ha true (83*2^376) 1 (-83/256) (by
    simp only [Bool.true_eq,if_true,he,neg_div]
    norm_num) hok context_good
  exact (refresh_sound context_good h).congr (fun t _ => by ring)

end ThomsonNegative.Certificate.Correction

namespace ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open ThomsonNegative.Compact.Packed

noncomputable def buildArgument (height : TM) (center : ℕ) : TM :=
  refresh context (addC context true (83*2^376) 1
    (collapseAt sourceContext context false center height))

theorem buildArgument_sound {height : TM} {a : ℝ → ℝ}
    (ha : Encl sourceContext height a) (center : ℕ)
    (hok : (buildArgument height center).ok=true) :
    Encl context (buildArgument height center) (fun t => a t-83/256) := by
  have hrefresh (c : Ctx) (A : TM) : (refresh c A).ok=A.ok := rfl
  rw [buildArgument,hrefresh] at hok
  have hc : (collapseAt sourceContext context false center height).ok=true :=
    addC_ok (c := context) (A := collapseAt sourceContext context false center height)
      (ng := true) (mag := 83*2^376) (dq := 1) hok
  exact shiftedHeight_sound
    (collapseAt_sound Compact.Target.Cells.context_good context_good ha false center hc) hok

end ThomsonNegative.Certificate.Correction
