import AllS.Units.N_GI.N_cube_k6.N_triangle_face_pair

set_option maxHeartbeats 300000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

def singleVertexPairLabels (a b : Fin 3 → Fin 8) : Fin 5 → Fin 8 :=
  ![a 0,a 1,a 2,b 1,b 2]

theorem singleVertexPairLabels_injective (a b : Fin 3 → Fin 8)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hab : ∀i j,a i=b j → i=0 ∧ j=0) :
    Function.Injective (singleVertexPairLabels a b) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals try rfl
  all_goals dsimp [singleVertexPairLabels] at hij
  all_goals first
    | have hh := ha hij; have hn := congrArg Fin.val hh; norm_num at hn
    | have hh := hb hij; have hn := congrArg Fin.val hh; norm_num at hn
    | have hh := hab _ _ hij; norm_num [Fin.ext_iff] at hh
    | have hh := hab _ _ hij.symm; norm_num [Fin.ext_iff] at hh

theorem single_vertex_triangles_labeling {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f g : TriFace Y c hY hc)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc,C.StrictSupport)
    (v : Fin 8) (hinter : triFaceVertices f∩triFaceVertices g={v}) :
    ∃ e : Equiv.Perm (Fin 8),triFaceVertices f={e 0,e 1,e 2} ∧
      triFaceVertices g={e 0,e 3,e 4} ∧
      (∀i,i≠0 → i.val<5 → inner ℝ (Y (e 0)) (Y (e i))=c) := by
  have hv : v∈triFaceVertices f∩triFaceVertices g := by rw [hinter];exact Finset.mem_singleton_self _
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hv).1
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hv).2
  let a := fun k : Fin 3 => triFaceVertex f (k+i)
  let b := fun k : Fin 3 => triFaceVertex g (k+j)
  have ha : Function.Injective a := by
    intro p q hpq
    exact add_right_cancel (triFaceVertex_injective f hsupport hpq)
  have hb : Function.Injective b := by
    intro p q hpq
    exact add_right_cancel (triFaceVertex_injective g hsupport hpq)
  have ha0 : a 0=v := by simpa only [a,zero_add] using hi
  have hb0 : b 0=v := by simpa only [b,zero_add] using hj
  have hab (p q : Fin 3) (he : a p=b q) : p=0 ∧ q=0 := by
    have hm : a p∈triFaceVertices f∩triFaceVertices g := by
      refine Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨p+i,Finset.mem_univ _,rfl⟩,?_⟩
      exact Finset.mem_image.mpr ⟨q+j,Finset.mem_univ _,he.symm⟩
    rw [hinter,Finset.mem_singleton] at hm
    exact ⟨ha (hm.trans ha0.symm),hb (he.symm.trans (hm.trans hb0.symm))⟩
  let inc : Fin 5 → Fin 8 := fun i => ⟨i.val,lt_trans i.isLt (by decide)⟩
  have hiinc : Function.Injective inc := by
    intro p q hpq
    exact Fin.ext (congrArg (fun k : Fin 8 => k.val) hpq)
  obtain ⟨e,he⟩ := Equiv.Perm.exists_extending_pair inc (singleVertexPairLabels a b) hiinc
    (singleVertexPairLabels_injective a b ha hb hab)
  have h0 : e 0=a 0 := he 0
  have h1 : e 1=a 1 := he 1
  have h2 : e 2=a 2 := he 2
  have h3 : e 3=b 1 := he 3
  have h4 : e 4=b 2 := he 4
  have h0b : e 0=b 0 := h0.trans (ha0.trans hb0.symm)
  have haf : Finset.univ.image a=triFaceVertices f := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_image.mpr ⟨p+i,Finset.mem_univ _,rfl⟩
    · rw [Finset.card_image_of_injective _ ha,Finset.card_univ,Fintype.card_fin,triFaceVertices_card f hsupport]
  have hbg : Finset.univ.image b=triFaceVertices g := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_image.mpr ⟨p+j,Finset.mem_univ _,rfl⟩
    · rw [Finset.card_image_of_injective _ hb,Finset.card_univ,Fintype.card_fin,triFaceVertices_card g hsupport]
  refine ⟨e,?_,?_,?_⟩
  · rw [←haf,show (Finset.univ : Finset (Fin 3))={0,1,2} by decide]
    simp only [Finset.image_insert,Finset.image_singleton,h0,h1,h2]
  · rw [←hbg,show (Finset.univ : Finset (Fin 3))={0,1,2} by decide]
    simp only [Finset.image_insert,Finset.image_singleton,h0b,h3,h4]
  · intro k hk0 hk5
    have hcontacta (p : Fin 3) (hp : p≠0) : inner ℝ (Y (a 0)) (Y (a p))=c := by
      apply triFaceVertex_contact f
      intro hh
      have heq : (0:Fin 3)=p := add_right_cancel hh
      exact hp heq.symm
    have hcontactb (p : Fin 3) (hp : p≠0) : inner ℝ (Y (b 0)) (Y (b p))=c := by
      apply triFaceVertex_contact g
      intro hh
      have heq : (0:Fin 3)=p := add_right_cancel hh
      exact hp heq.symm
    fin_cases k
    all_goals try norm_num [Fin.ext_iff] at hk0
    all_goals try norm_num [Fin.ext_iff] at hk5
    all_goals first
      | (convert hcontacta 1 (by decide) using 1 <;> simp only [←h0,←h1] <;> congr 2 <;> decide)
      | (convert hcontacta 2 (by decide) using 1 <;> simp only [←h0,←h2] <;> congr 2 <;> decide)
      | (convert hcontactb 1 (by decide) using 1 <;> simp only [←h0b,←h3] <;> congr 2 <;> decide)
      | (convert hcontactb 2 (by decide) using 1 <;> simp only [←h0b,←h4] <;> congr 2 <;> decide)

#print axioms single_vertex_triangles_labeling
end Blueprint.Thomson.Tail.Implementation
