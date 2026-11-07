import AllS.Units.N_GI.N_auxiliary_graphs.N_assemble
import Mathlib.Logic.Equiv.Fintype

set_option maxHeartbeats 3000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

def triplePairLabels (a b : Fin 3 → Fin 8) : Fin 6 → Fin 8 :=
  ![a 0,a 1,a 2,b 0,b 1,b 2]

theorem triplePairLabels_injective (a b : Fin 3 → Fin 8)
    (ha : Function.Injective a) (hb : Function.Injective b) (hab : ∀ i j,a i≠b j) :
    Function.Injective (triplePairLabels a b) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals try rfl
  all_goals dsimp [triplePairLabels] at hij
  all_goals first
    | exact (hab _ _ hij).elim
    | exact (hab _ _ hij.symm).elim
    | have hh := ha hij; have hn := congrArg Fin.val hh; norm_num at hn
    | have hh := hb hij; have hn := congrArg Fin.val hh; norm_num at hn

theorem disjoint_triangles_labeling {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f g : TriFace Y c hY hc)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc,C.StrictSupport)
    (hdis : Disjoint (triFaceVertices f) (triFaceVertices g)) :
    ∃ e : Equiv.Perm (Fin 8),e 0=triFaceVertex f 0 ∧ e 1=triFaceVertex f 1 ∧
      e 2=triFaceVertex f 2 ∧ e 3=triFaceVertex g 0 ∧ e 4=triFaceVertex g 1 ∧ e 5=triFaceVertex g 2 := by
  have hab (i j : Fin 3) : triFaceVertex f i≠triFaceVertex g j := by
    intro he
    exact Finset.disjoint_left.mp hdis
      (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
      (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,he.symm⟩)
  let inc : Fin 6 → Fin 8 := fun i => ⟨i.val,lt_trans i.isLt (by decide)⟩
  have hi : Function.Injective inc := by
    intro i j hij
    exact Fin.ext (congrArg (fun k : Fin 8 => k.val) hij)
  obtain ⟨e,he⟩ := Equiv.Perm.exists_extending_pair inc
    (triplePairLabels (triFaceVertex f) (triFaceVertex g)) hi
    (triplePairLabels_injective _ _ (triFaceVertex_injective f hsupport)
      (triFaceVertex_injective g hsupport) hab)
  exact ⟨e,he 0,he 1,he 2,he 3,he 4,he 5⟩

theorem triFace_pair_indicator {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f g : TriFace Y c hY hc) (hfg : f≠g)
    (hfaces : ∀ h : TriFace Y c hY hc,h=f ∨ h=g)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc,C.StrictSupport) (v : Fin 8) :
    faceCornerCount (boundaryArray Y c hY hc 3) v=
      (if v∈triFaceVertices f then 1 else 0)+(if v∈triFaceVertices g then 1 else 0) := by
  rw [triangle_incidence_indicator hsupport v]
  have huniv : (Finset.univ : Finset (TriFace Y c hY hc))={f,g} := by
    apply Finset.ext
    intro h
    simp only [Finset.mem_univ,Finset.mem_insert,Finset.mem_singleton,true_iff]
    exact hfaces h
  rw [huniv,Finset.sum_pair hfg]

theorem two_triangles_exhaust (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc,C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=6) :
    ∃ f g : TriFace Y c hY hc,f≠g ∧ ∀ h : TriFace Y c hY hc,h=f ∨ h=g := by
  have he := sphere_euler_assemble Y c hY hc hcupper hirr hbound hne hsupport
  have hT : Fintype.card (TriFace Y c hY hc)=2 := by
    have hh := he.2.2.1
    rw [hk] at hh
    exact hh
  have huniv : (Finset.univ : Finset (TriFace Y c hY hc)).card=2 := by simpa using hT
  obtain ⟨f,g,hfg,hpair⟩ := Finset.card_eq_two.mp huniv
  refine ⟨f,g,hfg,?_⟩
  intro h
  have hm : h∈({f,g} : Finset (TriFace Y c hY hc)) := hpair ▸ Finset.mem_univ h
  simpa only [Finset.mem_insert,Finset.mem_singleton] using hm

#print axioms disjoint_triangles_labeling
#print axioms triFace_pair_indicator
#print axioms two_triangles_exhaust
end Blueprint.Thomson.Tail.Implementation
