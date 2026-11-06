import AllS.Units.N_GI.N_auxiliary_graphs.N_shared_triangle_degrees
import AllS.Units.N_GI.N_cubic_quads.N_assemble
import Lean_Code.ContactTilingRigidity

set_option maxHeartbeats 3000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

def actualContactGraph (Y : Fin 8 → Point) (c : ℝ) : SimpleGraph (Fin 8) where
  Adj := ContactAdj Y c
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem cube_k08_all_equal (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=0) :
    ∀ v, Fintype.card (ContactNeighbor Y c v)=4 ∧
      faceCornerCount (boundaryArray Y c hY hc 3) v=3 := by
  have ha := covering_no_rattlers Y c hY hc hcupper hirr hbound hne hsupport
  have hd (v : Fin 8) : Fintype.card (ContactNeighbor Y c v)=4 := by
    have hh := degree_degree_four Y c hY hc.1 hcupper hirr hbound v (ha v)
    rw [←contactNeighbor_card_eq] at hh
    have hnot : Fintype.card (ContactNeighbor Y c v)≠3 := by
      intro h3
      have hm : v ∈ degreeThreeVertices Y c := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h3⟩
      have hp := Finset.card_pos.mpr ⟨v,hm⟩
      omega
    omega
  have hsum := auxiliary_graphs_incidence_identity Y c hY hc hcupper hirr hbound hne hsupport
  have hH : (Finset.univ.filter (fun w => Fintype.card (ContactNeighbor Y c w)=3 ∧
      faceCornerCount (boundaryArray Y c hY hc 3) w=1)).card=0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    have h3 := (Finset.mem_filter.mp hw).2.1
    have h4 := hd w
    omega
  change (∑ w, if Fintype.card (ContactNeighbor Y c w)=4 then
      3-faceCornerCount (boundaryArray Y c hY hc 3) w else 0)=_ at hsum
  rw [hH] at hsum
  intro v
  refine ⟨hd v,?_⟩
  have hle := Finset.single_le_sum (fun w (_ : w ∈ (Finset.univ : Finset (Fin 8))) =>
    Nat.zero_le (if Fintype.card (ContactNeighbor Y c w)=4 then
      3-faceCornerCount (boundaryArray Y c hY hc 3) w else 0)) (Finset.mem_univ v)
  rw [hsum,if_pos (hd v)] at hle
  have ht : faceCornerCount (boundaryArray Y c hY hc 3) v≤3 :=
    ((rhombus_angles_assemble Y c hY hc hcupper hirr hbound hne hsupport).1 v).2 (hd v)
  omega

theorem cube_k08_zero_height (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=0) : c=aInf := by
  let D := tiling_data_construct_existing_data Y c hY hc hcupper hirr hbound hne hsupport
  have heuler := sphere_euler_assemble Y c hY hc hcupper hirr hbound hne hsupport
  have hQ : D.quadCount=2 := by
    have hh := heuler.2.2.2.1
    rw [hk] at hh
    change 2*D.quadCount=4+0 at hh
    omega
  let f : Fin D.quadCount := ⟨0,by omega⟩
  have hE := cube_k08_all_equal Y c hY hc hcupper hirr hbound hne hsupport hk
  have hang (j : Fin 4) : D.angle f j=D.beta :=
    ((rhombus_angles_assemble Y c hY hc hcupper hirr hbound hne hsupport).2 f j).1
      (hE (D.quad f j)).1 (hE (D.quad f j)).2
  have htan := (rhombus_angles_alternating D hY hc f).2.2
  rw [hang 0,hang 1,←pow_two] at htan
  have hα := equilateral_angle_Ioo c hc
  have hcorner := (D.corner_geometry hY hc f 0).1
  rw [hang 0] at hcorner
  have hβ : D.beta ∈ Set.Ioo (0:ℝ) Real.pi := by
    change 0<D.alpha ∧ D.alpha<Real.pi/2 at hα
    constructor <;> linarith [Real.pi_pos,hα.1,hα.2,hcorner.1,hcorner.2]
  have hratio0 : 0<c/(1+c) := div_pos hc.1 (by linarith [hc.1])
  have hratio1 : c/(1+c)<1 := (div_lt_one (by linarith [hc.1])).mpr (by linarith)
  have hcos : Real.cos D.alpha=c/(1+c) := Real.cos_arccos (by linarith) hratio1.le
  have hid := packing_tan_polynomial_identity c D.alpha D.beta hc hcos rfl hβ
  rw [htan] at hid
  have hcne : c≠0 := hc.1.ne'
  have hden : (1-c)^2*(1+2*c)≠0 := by
    have h1 : 0<1-c := by linarith [hc.2]
    have h2 : 0<1+2*c := by linarith [hc.1]
    exact mul_ne_zero (pow_ne_zero 2 h1.ne') h2.ne' 
  have hpoly : 7*c^2+2*c-1=0 := by
    have hz : (1+c)*(7*c^2+2*c-1)=0 := by
      have hh : (1+c)*(7*c^2+2*c-1)/((1-c)^2*(1+2*c))=0 := by
        rw [←hid]
        field_simp [hcne]
        ring
      exact (div_eq_zero_iff.mp hh).resolve_right hden
    rcases mul_eq_zero.mp hz with h | h
    · linarith [hc.1]
    · exact h
  have ha := aInf_quadratic
  have hap := aInf_mem_Ioo.1
  have hfactor : (c-aInf)*(7*(c+aInf)+2)=0 := by nlinarith
  rcases mul_eq_zero.mp hfactor with h | h
  · exact sub_eq_zero.mp h
  · linarith [hc.1]

theorem cube_k08_zero_rigid (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=0) : SquareAntiprismVerification.Congruent Y P := by
  have heq := cube_k08_zero_height Y c hY hc hcupper hirr hbound hne hsupport hk
  subst c
  exact contact_tiling_rigidity Y hY hbound
    (tiling_data_construct_existing_data Y aInf hY hc hcupper hirr hbound hne hsupport)
    (tiling_data_boundary_adjacency Y aInf hY hc hcupper hirr hbound hne hsupport)

#print axioms cube_k08_all_equal
#print axioms cube_k08_zero_height
#print axioms cube_k08_zero_rigid
end Blueprint.Thomson.Tail.Implementation
