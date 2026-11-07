import AllS.Units.N_GI.N_cube_k08.N_all_equal
import Lean_Code.Infinitesimal

set_option maxHeartbeats 3000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

def packingCubeIndex (v : CubeVertex) : Fin 8 :=
  if v.1=0 then ![0,2,4,6] v.2 else ![5,7,3,1] v.2

def packingCubeEquiv : CubeVertex ≃ Fin 8 :=
  Equiv.ofBijective packingCubeIndex (by decide)

theorem packingCube_contacts (i j : Fin 4) (hij : i≠j) :
    inner ℝ (P (packingCubeIndex (0,i))) (P (packingCubeIndex (1,j)))=aInf := by
  unfold P
  rw [X_eq_Xc]
  have hs2 : Real.sqrt (2:ℝ)^2=2 := Real.sq_sqrt (by norm_num)
  have hra : Real.sqrt (1-aInf)^2=1-aInf := Real.sq_sqrt (by linarith [aInf_mem_Ioo.2])
  have hha : Real.sqrt aInf^2=aInf := Real.sq_sqrt aInf_mem_Ioo.1.le
  have hrel : (1-aInf)*Real.sqrt 2=4*aInf := by
    unfold aInf
    nlinarith
  have hrr : Real.sqrt (1-aInf)^2*Real.sqrt 2=4*aInf := by rw [hra,hrel]
  fin_cases i <;> fin_cases j
  all_goals try exact (hij rfl).elim
  all_goals simp [packingCubeIndex,Xc,inner_vec3,r,h]
  all_goals nlinarith [hs2,hra,hha,hrel,hrr]

theorem congruent_packing_has_cube (Y : Fin 8 → Point)
    (h : SquareAntiprismVerification.Congruent Y P) :
    HasSpanningCube (actualContactGraph Y aInf) := by
  obtain ⟨U,σ,hσ⟩ := h
  let e : CubeVertex ≃ Fin 8 := packingCubeEquiv.trans σ
  refine ⟨e,?_⟩
  intro i j hij
  constructor
  · intro he
    have hp := e.injective he
    have h01 := congrArg Prod.fst hp
    norm_num at h01
  · have hinner := U.inner_map_map (Y (e (0,i))) (Y (e (1,j)))
    have hi : P (packingCubeIndex (0,i))=U (Y (e (0,i))) := hσ _
    have hj : P (packingCubeIndex (1,j))=U (Y (e (1,j))) := hσ _
    calc
      inner ℝ (Y (e (0,i))) (Y (e (1,j))) =
          inner ℝ (U (Y (e (0,i)))) (U (Y (e (1,j)))) := hinner.symm
      _ = inner ℝ (P (packingCubeIndex (0,i))) (P (packingCubeIndex (1,j))) :=
        congrArg₂ (inner ℝ) hi.symm hj.symm
      _ = aInf := packingCube_contacts i j hij

theorem cube_k08_delete_matching (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=0) :
    HasSpanningCube (actualContactGraph Y c) := by
  have hr := cube_k08_zero_rigid Y c hY hc hcupper hirr hbound hne hsupport hk
  have heq := cube_k08_zero_height Y c hY hc hcupper hirr hbound hne hsupport hk
  subst c
  exact congruent_packing_has_cube Y hr

#print axioms packingCube_contacts
#print axioms congruent_packing_has_cube
#print axioms cube_k08_delete_matching
end Blueprint.Thomson.Tail.Implementation
