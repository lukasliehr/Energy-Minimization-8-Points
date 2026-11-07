import AllS.Units.N_GI.N_cubic_quads.N_eighth_vertex

set_option maxHeartbeats 3000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

abbrev CubeVertex := Fin 2 × Fin 4

def HasSpanningCube (G : SimpleGraph (Fin 8)) : Prop :=
  ∃ e : CubeVertex ≃ Fin 8, ∀ i j : Fin 4, i≠j → G.Adj (e (0,i)) (e (1,j))

def cubicCubeLabel (Q : CubicQuadData) (o z : Fin 8) (v : CubeVertex) : Fin 8 :=
  if v.1=0 then ![o,Q.rootOpposite o 0,Q.rootOpposite o 1,Q.rootOpposite o 2] v.2
  else ![z,Q.rootNeighbor o 2,Q.rootNeighbor o 0,Q.rootNeighbor o 1] v.2

theorem cubicCubeLabel_injective (Q : CubicQuadData) (o z : Fin 8)
    (hz : ∀ j, Q.rootSeven o j≠z) : Function.Injective (cubicCubeLabel Q o z) := by
  have hz0 : o≠z := hz 0
  have hza (i : Fin 3) : Q.rootNeighbor o i≠z := by
    obtain ⟨j,hj⟩ := Q.rootSeven_contains_neighbor o i
    exact fun h => hz j (hj.trans h)
  have hzx (i : Fin 3) : Q.rootOpposite o i≠z := by
    obtain ⟨j,hj⟩ := Q.rootSeven_contains_opposite o i
    exact fun h => hz j (hj.trans h)
  rintro ⟨i,j⟩ ⟨k,l⟩ hij
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l
  all_goals try rfl
  all_goals dsimp [cubicCubeLabel] at hij
  all_goals first
    | exact (hz0 hij).elim
    | exact (hz0 hij.symm).elim
    | exact ((hza _) hij).elim
    | exact ((hza _) hij.symm).elim
    | exact ((hzx _) hij).elim
    | exact ((hzx _) hij.symm).elim
    | exact ((Q.rootNeighbor_ne_root o _) hij).elim
    | exact ((Q.rootNeighbor_ne_root o _) hij.symm).elim
    | exact ((Q.rootOpposite_ne_root o _) hij).elim
    | exact ((Q.rootOpposite_ne_root o _) hij.symm).elim
    | exact ((Q.rootOpposite_ne_neighbor o _ _) hij).elim
    | exact ((Q.rootOpposite_ne_neighbor o _ _) hij.symm).elim
    | have hh := Q.rootNeighbor_injective o hij; have hn := congrArg Fin.val hh; norm_num at hn
    | have hh := Q.rootOpposite_injective o hij; have hn := congrArg Fin.val hh; norm_num at hn

theorem cubicCubeLabel_contacts (Q : CubicQuadData) (o z : Fin 8)
    (hz : ∀ i, Q.graph.Adj z (Q.rootOpposite o i)) :
    ∀ i j : Fin 4, i≠j → Q.graph.Adj (cubicCubeLabel Q o z (0,i)) (cubicCubeLabel Q o z (1,j)) := by
  have h0 := cubic_quads_root_faces Q o 0
  have h1 := cubic_quads_root_faces Q o 1
  have h2 := cubic_quads_root_faces Q o 2
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals try exact (hij rfl).elim
  all_goals dsimp [cubicCubeLabel]
  all_goals first
    | exact h0.1
    | exact h1.1
    | exact h2.1
    | exact h0.2.1.symm
    | exact h1.2.1.symm
    | exact h2.2.1.symm
    | exact h0.2.2.1
    | exact h1.2.2.1
    | exact h2.2.2.1
    | exact (hz 0).symm
    | exact (hz 1).symm
    | exact (hz 2).symm

theorem cubic_quads_cube_labeling (Q : CubicQuadData) : HasSpanningCube Q.graph := by
  obtain ⟨z,hz,hneighbors⟩ := cubic_quads_eighth_vertex Q 0
  have hzadj (i : Fin 3) : Q.graph.Adj z (Q.rootOpposite 0 i) := by
    apply (Q.graph.mem_neighborFinset _ _).mp
    rw [hneighbors]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  let e : CubeVertex ≃ Fin 8 := Equiv.ofBijective (cubicCubeLabel Q 0 z)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨cubicCubeLabel_injective Q 0 z hz,by decide⟩)
  exact ⟨e,cubicCubeLabel_contacts Q 0 z hzadj⟩

#print axioms cubicCubeLabel_injective
#print axioms cubicCubeLabel_contacts
#print axioms cubic_quads_cube_labeling
end Blueprint.Thomson.Tail.Implementation
