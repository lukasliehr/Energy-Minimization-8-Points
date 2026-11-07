import AllS.Units.N_GI.N_disphenoid.N_facet_coordinates
import Mathlib.Tactic.Module

set_option maxHeartbeats 1200000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem positive_circumcenter_acute_inner_zero (T : Fin 3 → Point) (O : Point)
    (hT : AffineIndependent ℝ T) (w : Fin 3 → ℝ) (hwpos : 0<w 0)
    (hwsum : ∑i,w i=1) (hwrepr : ∑i,w i • T i=O)
    (hnorm : ∀i,‖T i-O‖^2=‖T 0-O‖^2) :
    0 < inner ℝ (T 1-T 0) (T 2-T 0) := by
  let x := T 0-O
  let y := T 1-O
  let z := T 2-O
  have hsum : w 0+w 1+w 2=1 := by simpa only [Fin.sum_univ_three] using hwsum
  have hrepr : w 0 • T 0+w 1 • T 1+w 2 • T 2=O := by
    simpa only [Fin.sum_univ_three] using hwrepr
  have hrel : w 0 • x+w 1 • y+w 2 • z=0 := by
    calc
      w 0 • x+w 1 • y+w 2 • z =
        (w 0 • T 0+w 1 • T 1+w 2 • T 2)-(w 0+w 1+w 2) • O := by dsimp [x,y,z];module
      _ = 0 := by rw [hrepr,hsum,one_smul,sub_self]
  have hm : y+z≠0 := by
    intro hm
    have hmean : T 1+T 2=(2:ℝ) • O := by
      calc
        T 1+T 2 = y+z+(2:ℝ) • O := by dsimp [y,z];module
        _ = (2:ℝ) • O := by rw [hm,zero_add]
    let w' : Fin 3 → ℝ := ![w 0,w 1-1/2,w 2-1/2]
    have hsum' : ∑i,w' i=0 := by
      rw [Fin.sum_univ_three]
      change w 0+(w 1-1/2)+(w 2-1/2)=0
      linarith
    have hrepr' : ∑i,w' i • T i=0 := by
      calc
        ∑i,w' i • T i = (w 0 • T 0+w 1 • T 1+w 2 • T 2)-(1/2:ℝ) • (T 1+T 2) := by
          rw [Fin.sum_univ_three]
          change w 0 • T 0+(w 1-1/2) • T 1+(w 2-1/2) • T 2=_
          module
        _ = 0 := by rw [hrepr,hmean];module
    have hz := hT.eq_zero_of_sum_eq_zero hsum' hrepr' 0 (Finset.mem_univ _)
    change w 0=0 at hz
    exact hwpos.ne' hz
  have hmp : 0 < inner ℝ (y+z) (y+z) := real_inner_self_pos.mpr hm
  have hy : inner ℝ y y=inner ℝ x x := by
    simpa only [real_inner_self_eq_norm_sq] using hnorm 1
  have hz : inner ℝ z z=inner ℝ x x := by
    simpa only [real_inner_self_eq_norm_sq] using hnorm 2
  have hi := congrArg (fun v => inner ℝ v (y+z)) hrel
  simp only [inner_add_left,inner_add_right,inner_smul_left,conj_trivial,inner_zero_left] at hi hmp
  have hxy : inner ℝ y x=inner ℝ x y := real_inner_comm _ _
  have hxz : inner ℝ z x=inner ℝ x z := real_inner_comm _ _
  have hyz : inner ℝ z y=inner ℝ y z := real_inner_comm _ _
  have hid : w 0 * inner ℝ (y-x) (z-x)=inner ℝ (y+z) (y+z)/2 := by
    simp only [inner_sub_left,inner_sub_right,inner_add_left,inner_add_right,hxy,hxz,hyz]
    simp only [hy,hz,hyz] at hi hmp ⊢
    have he : (w 0+w 1+w 2)*(inner ℝ x x+inner ℝ y z)=inner ℝ x x+inner ℝ y z := by rw [hsum,one_mul]
    nlinarith
  have hpos : 0 < inner ℝ (y-x) (z-x) := by
    apply (mul_pos_iff_of_pos_left hwpos).mp
    rw [hid]
    exact div_pos (real_inner_self_pos.mpr hm) (by norm_num)
  have h1 : y-x=T 1-T 0 := by dsimp [x,y];module
  have h2 : z-x=T 2-T 0 := by dsimp [x,z];module
  rwa [h1,h2] at hpos

#print axioms positive_circumcenter_acute_inner_zero
end Blueprint.Thomson.Tail.Implementation
