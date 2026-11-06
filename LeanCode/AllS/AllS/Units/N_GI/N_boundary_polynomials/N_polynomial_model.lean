import AllS.Units.N_G.N_boundary_basis
import AllS.Units.N_GI.N_constants.N_pair_table

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def boundaryRho : ℝ := 61/200

def boundaryContactRow (e : ContactIndex) (j : Fin 13) : ℝ :=
  -2*(inner ℝ (packingReference (contactNext e)) (boundaryPhysical j e.1)+
      inner ℝ (packingReference e.1) (boundaryPhysical j (contactNext e)))

def boundaryContactT (e : ContactIndex) (j l : Fin 13) : ℝ :=
  inner ℝ (boundaryPhysical j e.1) (boundaryPhysical l e.1)+
    inner ℝ (boundaryPhysical j (contactNext e)) (boundaryPhysical l (contactNext e))

def boundaryContactM (e : ContactIndex) (j l : Fin 13) : ℝ :=
  packingHeight*boundaryContactT e j l-
    inner ℝ (boundaryPhysical j e.1) (boundaryPhysical l (contactNext e))-
    inner ℝ (boundaryPhysical j (contactNext e)) (boundaryPhysical l e.1)

def boundaryContactPolynomial (e : ContactIndex) (y : Fin 13 → ℝ) : ℝ :=
  gap+boundaryRho*(∑j,boundaryContactRow e j*y j)+
    boundaryRho^2*(∑j,∑l,y j*(boundaryContactM e j l+(gap/2)*boundaryContactT e j l)*y l)

def boundaryDisplacement (y : Fin 13 → ℝ) (i : Fin 8) : Point :=
  boundaryRho • tangentVector (boundarySynthesis y) i

theorem boundaryDisplacement_expansion (y : Fin 13 → ℝ) (i : Fin 8) :
    boundaryDisplacement y i=boundaryRho • (∑j,y j • boundaryPhysical j i) := by
  rw [boundaryDisplacement,boundarySynthesis_tangent]

theorem boundaryDisplacement_dot (y : Fin 13 → ℝ) (i k : Fin 8) :
    inner ℝ (boundaryDisplacement y i) (boundaryDisplacement y k)=
      boundaryRho^2*(∑j,∑l,y j*inner ℝ (boundaryPhysical j i) (boundaryPhysical l k)*y l) := by
  rw [boundaryDisplacement_expansion,boundaryDisplacement_expansion]
  simp only [inner_smul_left,inner_smul_right,starRingEnd_apply,star_trivial]
  have hh : inner ℝ (∑j,y j • boundaryPhysical j i) (∑l,y l • boundaryPhysical l k)=
      ∑j,∑l,y j*inner ℝ (boundaryPhysical j i) (boundaryPhysical l k)*y l := by
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro j _
    simp only [inner_smul_left,starRingEnd_apply,star_trivial,inner_sum,inner_smul_right,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hh]
  ring

set_option maxHeartbeats 2000000 in
theorem boundaryContactPolynomial_physical (e : ContactIndex) (y : Fin 13 → ℝ) :
    boundaryContactPolynomial e y=
      gap-2*(inner ℝ (packingReference e.1) (boundaryDisplacement y (contactNext e))+
        inner ℝ (packingReference (contactNext e)) (boundaryDisplacement y e.1))+
      (packingHeight+gap/2)*(‖boundaryDisplacement y e.1‖^2+‖boundaryDisplacement y (contactNext e)‖^2)-
      2*inner ℝ (boundaryDisplacement y e.1) (boundaryDisplacement y (contactNext e)) := by
  have hlin : boundaryRho*(∑j,boundaryContactRow e j*y j)=
      -2*(inner ℝ (packingReference e.1) (boundaryDisplacement y (contactNext e))+
        inner ℝ (packingReference (contactNext e)) (boundaryDisplacement y e.1)) := by
    simp only [boundaryContactRow,boundaryDisplacement_expansion,inner_smul_right,inner_sum,
      mul_add,add_mul,Finset.mul_sum,Finset.sum_mul]
    simp only [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hquad : boundaryRho^2*(∑j,∑l,y j*(boundaryContactM e j l+(gap/2)*boundaryContactT e j l)*y l)=
      (packingHeight+gap/2)*(‖boundaryDisplacement y e.1‖^2+‖boundaryDisplacement y (contactNext e)‖^2)-
      inner ℝ (boundaryDisplacement y e.1) (boundaryDisplacement y (contactNext e))-
      inner ℝ (boundaryDisplacement y (contactNext e)) (boundaryDisplacement y e.1) := by
    rw [←real_inner_self_eq_norm_sq,←real_inner_self_eq_norm_sq,boundaryDisplacement_dot,
      boundaryDisplacement_dot,boundaryDisplacement_dot,boundaryDisplacement_dot]
    simp only [boundaryContactM,boundaryContactT,mul_add,add_mul,mul_sub,sub_mul,
      Finset.mul_sum,Finset.sum_mul]
    simp only [←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [boundaryContactPolynomial,hlin,hquad,real_inner_comm (boundaryDisplacement y (contactNext e)) (boundaryDisplacement y e.1)]
  ring

#print axioms boundaryContactPolynomial_physical
end Blueprint.Thomson.Tail.Implementation
