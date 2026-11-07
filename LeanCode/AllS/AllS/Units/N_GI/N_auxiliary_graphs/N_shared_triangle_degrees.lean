import AllS.Units.N_GI.N_covering.N_facial_cliques
import AllS.Units.N_GI.N_auxiliary_graphs.N_incidence_identity

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

def triangleFlagCount {n : ℕ} (b : Fin n → Bool) : ℕ := ∑ i, if b i then 1 else 0

def sharedFourFlags (b : Fin 4 → Bool) (i : Fin 4) : Bool := b i && b (i+1)
def sharedThreeFlags (b : Fin 3 → Bool) (i : Fin 3) : Bool := b i && b (i+1)

theorem sharedFourFlags_exact : ∀ b : Fin 4 → Bool, triangleFlagCount b ≤ 3 →
    (triangleFlagCount b=3 → triangleFlagCount (sharedFourFlags b)=2) ∧
    (triangleFlagCount b≤2 → triangleFlagCount (sharedFourFlags b)≤1) ∧
    (triangleFlagCount b≤1 → triangleFlagCount (sharedFourFlags b)=0) ∧
    (∀ i j : Fin 4, i≠j → sharedFourFlags b i=true → sharedFourFlags b j=true →
      i+1=j ∨ j+1=i) := by decide

theorem sharedThreeFlags_zero : ∀ b : Fin 3 → Bool, triangleFlagCount b ≤ 1 →
    triangleFlagCount (sharedThreeFlags b)=0 := by decide

def contactFaceKey {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (d : ContactDart Y c) :
    PermutationOrbit (contactFaceNext Y c hY hc) := Quotient.mk _ d

def contactTriangleFlag {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (d : ContactDart Y c) : Bool :=
  decide ((boundaryOrbitCycle Y c hY hc (contactFaceKey hY hc d)).size+1=3)

theorem contactFaceKey_next {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (d : ContactDart Y c) :
    contactFaceKey hY hc (contactFaceNext Y c hY hc d)=contactFaceKey hY hc d := by
  apply Quotient.sound
  have h : (contactFaceNext Y c hY hc).SameCycle d (contactFaceNext Y c hY hc d) := by
    simpa using sameCycle_iterate (contactFaceNext Y c hY hc) d 1
  exact h.symm

theorem contactTriangleFlag_next {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (d : ContactDart Y c) :
    contactTriangleFlag hY hc (contactFaceNext Y c hY hc d)=contactTriangleFlag hY hc d := by
  unfold contactTriangleFlag
  rw [contactFaceKey_next]

def contactSectorTriangleFlag {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (v : Fin 8) (q : ContactNeighbor Y c v) : Bool :=
  contactTriangleFlag hY hc (contactReverse Y c ⟨v,q⟩)

theorem contactSectorTriangleFlag_rotate {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (v : Fin 8) (q : ContactNeighbor Y c v) :
    contactSectorTriangleFlag hY hc v (contactRotateAt Y c hY hc v q)=
      contactTriangleFlag hY hc ⟨v,q⟩ := by
  have h := contactTriangleFlag_next hY hc
    (contactReverse Y c (contactRotate Y c hY hc ⟨v,q⟩))
  have he : contactFaceNext Y c hY hc
      (contactReverse Y c (contactRotate Y c hY hc ⟨v,q⟩))=⟨v,q⟩ := by
    change (contactRotate Y c hY hc).symm
      (contactReverse Y c (contactReverse Y c (contactRotate Y c hY hc ⟨v,q⟩)))=⟨v,q⟩
    change (contactRotate Y c hY hc).symm (contactRotate Y c hY hc ⟨v,q⟩)=⟨v,q⟩
    exact Equiv.symm_apply_apply _ _
  rw [he] at h
  exact h.symm


theorem contactTriangleFlag_orbit_point {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (f : PermutationOrbit (contactFaceNext Y c hY hc))
    (i : Fin ((boundaryOrbitCycle Y c hY hc f).size+1)) :
    contactTriangleFlag hY hc ((boundaryOrbitCycle Y c hY hc f).point i) =
      decide ((boundaryOrbitCycle Y c hY hc f).size+1=3) := by
  have h := orbitPermutationCycle_class (contactFaceNext Y c hY hc) f i
  unfold contactTriangleFlag contactFaceKey
  exact congrArg (fun q => decide ((boundaryOrbitCycle Y c hY hc q).size+1=3)) h

theorem contactTriangleFlag_weighted_sum {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (w : Fin 8 → ℕ) :
    (∑ f, ∑ j, w (boundaryArray Y c hY hc 3 f j)) =
      ∑ d : ContactDart Y c, if contactTriangleFlag hY hc d then w d.1 else 0 := by
  classical
  let len := fun f => (boundaryOrbitCycle Y c hY hc f).size+1
  calc
    _ = ∑ f : BoundaryOfLength Y c hY hc 3, ∑ i,
        w ((boundaryOrbitCycle Y c hY hc f.val).vertex i) := tiling_data_array_sum Y c hY hc 3 w
    _ = ∑ f ∈ Finset.univ.filter (fun f => len f=3), ∑ i,
        w ((boundaryOrbitCycle Y c hY hc f).vertex i) :=
      (Finset.sum_subtype (p:=fun f => len f=3) (Finset.univ.filter (fun f => len f=3))
        (by intro f; simp only [Finset.mem_filter,Finset.mem_univ,true_and])
        (fun f => ∑ i, w ((boundaryOrbitCycle Y c hY hc f).vertex i))).symm
    _ = ∑ f, if len f=3 then ∑ i,
        w ((boundaryOrbitCycle Y c hY hc f).vertex i) else 0 := by rw [Finset.sum_filter]
    _ = ∑ f, ∑ i, if contactTriangleFlag hY hc ((boundaryOrbitCycle Y c hY hc f).point i)
        then w ((boundaryOrbitCycle Y c hY hc f).vertex i) else 0 := by
      apply Finset.sum_congr rfl
      intro f _
      simp only [contactTriangleFlag_orbit_point, decide_eq_true_eq]
      by_cases h : len f=3
      · simp only [len] at h
        simp only [len,h,↓reduceIte]
      · simp only [len] at h
        simp only [len,h,↓reduceIte,Finset.sum_const_zero]
    _ = _ := sum_over_permutation_cycles (contactFaceNext Y c hY hc)
      (fun d => if contactTriangleFlag hY hc d then w d.1 else 0)

theorem contactTriangleFlag_vertex_count {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (v : Fin 8) :
    (∑ q : ContactNeighbor Y c v, if contactTriangleFlag hY hc ⟨v,q⟩ then 1 else 0) =
      faceCornerCount (boundaryArray Y c hY hc 3) v := by
  classical
  have h := contactTriangleFlag_weighted_sum hY hc (fun i => if i=v then 1 else 0)
  have hr : (∑ d : ContactDart Y c, if contactTriangleFlag hY hc d then
      (if d.1=v then 1 else 0) else 0) =
      ∑ q : ContactNeighbor Y c v, if contactTriangleFlag hY hc ⟨v,q⟩ then 1 else 0 := by
    rw [Fintype.sum_sigma,Finset.sum_eq_single v]
    · simp
    · intro i _ hiv
      simp [hiv]
    · simp
  rw [hr] at h
  simpa only [faceCornerCount,faceCornersAt,Finset.card_filter,Fintype.sum_prod_type] using h.symm

theorem contactSectorTriangleFlag_vertex_count {Y : Fin 8 → Point} {c : ℝ}
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (v : Fin 8) :
    (∑ q : ContactNeighbor Y c v, if contactSectorTriangleFlag hY hc v q then 1 else 0) =
      faceCornerCount (boundaryArray Y c hY hc 3) v := by
  calc
    _ = ∑ q : ContactNeighbor Y c v,
        if contactSectorTriangleFlag hY hc v (contactRotateAt Y c hY hc v q) then 1 else 0 :=
      (Equiv.sum_comp (contactRotateAt Y c hY hc v) (fun q =>
        if contactSectorTriangleFlag hY hc v q then (1:ℕ) else 0)).symm
    _ = _ := by
      simp only [contactSectorTriangleFlag_rotate]
      exact contactTriangleFlag_vertex_count hY hc v


def SharedTriangleAdj {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (v w : Fin 8) : Prop :=
  ∃ q : ContactNeighbor Y c v, q.val=w ∧ contactTriangleFlag hY hc ⟨v,q⟩=true ∧
    contactTriangleFlag hY hc (contactReverse Y c ⟨v,q⟩)=true

def sharedTriangleGraph {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) : SimpleGraph (Fin 8) where
  Adj := SharedTriangleAdj hY hc
  symm := ⟨by
    rintro v w ⟨q,rfl,h1,h2⟩
    exact ⟨(contactReverse Y c ⟨v,q⟩).2,rfl,h2,h1⟩⟩
  loopless := ⟨by
    rintro v ⟨q,hq,_,_⟩
    exact q.property.1 hq⟩

def sharedTriangleNeighbors {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (v : Fin 8) : Finset (ContactNeighbor Y c v) :=
  Finset.univ.filter (fun q => contactTriangleFlag hY hc ⟨v,q⟩=true ∧
    contactTriangleFlag hY hc (contactReverse Y c ⟨v,q⟩)=true)

theorem sharedTriangleNeighborFinset_eq {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (v : Fin 8) :
    (sharedTriangleGraph hY hc).neighborFinset v = (sharedTriangleNeighbors hY hc v).image Subtype.val := by
  apply Finset.ext
  intro w
  rw [SimpleGraph.mem_neighborFinset]
  change SharedTriangleAdj hY hc v w ↔ _
  simp only [SharedTriangleAdj,Finset.mem_image,sharedTriangleNeighbors,
    Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨q,hq,h1,h2⟩
    exact ⟨q,⟨h1,h2⟩,hq⟩
  · rintro ⟨q,⟨h1,h2⟩,hq⟩
    exact ⟨q,hq,h1,h2⟩

theorem sharedTriangleGraph_degree_sum {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (v : Fin 8) :
    (sharedTriangleGraph hY hc).degree v = ∑ q : ContactNeighbor Y c v,
      if contactSectorTriangleFlag hY hc v q &&
        contactSectorTriangleFlag hY hc v (contactRotateAt Y c hY hc v q) then 1 else 0 := by
  rw [SimpleGraph.degree,sharedTriangleNeighborFinset_eq,
    Finset.card_image_of_injective _ Subtype.val_injective]
  simp only [sharedTriangleNeighbors,Finset.card_filter]
  apply Finset.sum_congr rfl
  intro q _
  rw [contactSectorTriangleFlag_rotate]
  simp only [contactSectorTriangleFlag,Bool.and_eq_true,and_comm]

theorem contactRotateAt_fin_cycle {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (v : Fin 8) (n : ℕ) [NeZero n]
    (hn : Fintype.card (ContactNeighbor Y c v)=n) :
    ∃ e : Fin n ≃ ContactNeighbor Y c v, ∀ i,
      contactRotateAt Y c hY hc v (e i)=e (i+1) := by
  have hpos : 0 < Fintype.card (ContactNeighbor Y c v) := hn.symm ▸ NeZero.pos n
  obtain ⟨q⟩ := Fintype.card_pos_iff.mp hpos
  have hne : ∃ j, j≠v ∧ inner ℝ (Y v) (Y j)=c := ⟨q,q.property⟩
  let D := Classical.choice (contact_order_exists Y c v hY hc hne)
  have hlen : D.size+1=n := by
    have h := Fintype.card_congr D.labelEquiv
    simpa only [Fintype.card_fin,hn] using h
  let e : Fin n ≃ ContactNeighbor Y c v := (finIndexEquiv hlen.symm).trans D.labelEquiv
  refine ⟨e,?_⟩
  intro i
  unfold contactRotateAt
  rw [dif_pos hne]
  change D.successor (D.labelEquiv (Fin.cast hlen.symm i))=
    D.labelEquiv (Fin.cast hlen.symm (i+1))
  rw [D.successor_label,fin_cast_add_one]

theorem sharedTriangleGraph_degree_three_zero {Y : Fin 8 → Point} {c : ℝ}
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (v : Fin 8)
    (hdegree : Fintype.card (ContactNeighbor Y c v)=3)
    (ht : faceCornerCount (boundaryArray Y c hY hc 3) v≤1) :
    (sharedTriangleGraph hY hc).degree v=0 := by
  obtain ⟨e,he⟩ := contactRotateAt_fin_cycle hY hc v 3 hdegree
  let b : Fin 3 → Bool := fun i => contactSectorTriangleFlag hY hc v (e i)
  have hcount : triangleFlagCount b=faceCornerCount (boundaryArray Y c hY hc 3) v :=
    (Equiv.sum_comp e (fun q => if contactSectorTriangleFlag hY hc v q then (1:ℕ) else 0)).trans
      (contactSectorTriangleFlag_vertex_count hY hc v)
  have hs : (sharedTriangleGraph hY hc).degree v=triangleFlagCount (sharedThreeFlags b) := by
    rw [sharedTriangleGraph_degree_sum,←Equiv.sum_comp e]
    simp only [triangleFlagCount,sharedThreeFlags,b,he]
    rfl
  rw [hs]
  exact sharedThreeFlags_zero b (hcount.trans_le ht)

theorem sharedTriangleGraph_degree_four_cases {Y : Fin 8 → Point} {c : ℝ}
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (v : Fin 8)
    (hdegree : Fintype.card (ContactNeighbor Y c v)=4)
    (ht : faceCornerCount (boundaryArray Y c hY hc 3) v≤3) :
    let t := faceCornerCount (boundaryArray Y c hY hc 3) v
    ((sharedTriangleGraph hY hc).degree v=2 ↔ t=3) ∧
    (t≤2 → (sharedTriangleGraph hY hc).degree v≤1) ∧
    (t≤1 → (sharedTriangleGraph hY hc).degree v=0) := by
  dsimp only
  obtain ⟨e,he⟩ := contactRotateAt_fin_cycle hY hc v 4 hdegree
  let b : Fin 4 → Bool := fun i => contactSectorTriangleFlag hY hc v (e i)
  have hcount : triangleFlagCount b=faceCornerCount (boundaryArray Y c hY hc 3) v :=
    (Equiv.sum_comp e (fun q => if contactSectorTriangleFlag hY hc v q then (1:ℕ) else 0)).trans
      (contactSectorTriangleFlag_vertex_count hY hc v)
  have hs : (sharedTriangleGraph hY hc).degree v=triangleFlagCount (sharedFourFlags b) := by
    rw [sharedTriangleGraph_degree_sum,←Equiv.sum_comp e]
    simp only [triangleFlagCount,sharedFourFlags,b,he]
    rfl
  have h := sharedFourFlags_exact b (hcount.trans_le ht)
  rw [hs,←hcount]
  refine ⟨⟨?_,h.1⟩,h.2.1,h.2.2.1⟩
  intro hh
  by_contra hne
  have hle : triangleFlagCount b≤2 := by omega
  have hbad := h.2.1 hle
  omega


theorem contactTriangleFlag_closing_contact {Y : Fin 8 → Point} {c : ℝ}
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hirr : PackingIrreducible c Y)
    (d : ContactDart Y c) (hflag : contactTriangleFlag hY hc d=true) :
    inner ℝ (Y d.1) (Y (contactFaceNext Y c hY hc d).2.val)=c := by
  obtain ⟨⟨f,i⟩,hi⟩ := (cyclePartitionMap_bijective (contactFaceNext Y c hY hc)).2 d
  let C := boundaryOrbitCycle Y c hY hc f
  change C.point i=d at hi
  have hlen : C.size+1=3 := by
    have hh := contactTriangleFlag_orbit_point hY hc f i
    rw [hi,hflag] at hh
    exact of_decide_eq_true hh.symm
  have hbase : C.vertex i=d.1 := congrArg Sigma.fst hi
  have hnext : C.point (i+1)=contactFaceNext Y c hY hc d :=
    (C.step i).symm.trans (congrArg (contactFaceNext Y c hY hc) hi)
  have htip : C.vertex (i+1+1)=(contactFaceNext Y c hY hc d).2.val :=
    (C.vertex_next (i+1)).trans (congrArg (fun e : ContactDart Y c => e.2.val) hnext)
  have hneq : i≠i+1+1 := by
    intro hh
    have he : d.1=(contactFaceNext Y c hY hc d).2.val :=
      hbase.symm.trans ((congrArg C.vertex hh).trans htip)
    exact contactFaceNext_no_backtrack Y c hY hc hirr d he.symm
  have hcontact := C.triangle_contacts hlen i (i+1+1) hneq
  exact (congrArg₂ (fun v w => inner ℝ (Y v) (Y w)) hbase htip).symm.trans hcontact

theorem contactSectorTriangleFlag_contact {Y : Fin 8 → Point} {c : ℝ}
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hirr : PackingIrreducible c Y)
    (v : Fin 8) (q : ContactNeighbor Y c v)
    (hflag : contactSectorTriangleFlag hY hc v (contactRotateAt Y c hY hc v q)=true) :
    inner ℝ (Y q) (Y (contactRotateAt Y c hY hc v q))=c := by
  have h := contactTriangleFlag_closing_contact hY hc hirr
    (contactReverse Y c (contactRotate Y c hY hc ⟨v,q⟩)) hflag
  have he : contactFaceNext Y c hY hc
      (contactReverse Y c (contactRotate Y c hY hc ⟨v,q⟩))=⟨v,q⟩ := by
    change (contactRotate Y c hY hc).symm
      (contactReverse Y c (contactReverse Y c (contactRotate Y c hY hc ⟨v,q⟩)))=⟨v,q⟩
    change (contactRotate Y c hY hc).symm (contactRotate Y c hY hc ⟨v,q⟩)=⟨v,q⟩
    exact Equiv.symm_apply_apply _ _
  rw [he] at h
  exact (real_inner_comm _ _).trans h

theorem sharedTriangleGraph_two_neighbors_contact {Y : Fin 8 → Point} {c : ℝ}
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hirr : PackingIrreducible c Y)
    (v x y : Fin 8) (hdegree : Fintype.card (ContactNeighbor Y c v)=4)
    (ht : faceCornerCount (boundaryArray Y c hY hc 3) v≤3) (hxy : x≠y)
    (hx : (sharedTriangleGraph hY hc).Adj v x) (hy : (sharedTriangleGraph hY hc).Adj v y) :
    inner ℝ (Y x) (Y y)=c := by
  obtain ⟨e,he⟩ := contactRotateAt_fin_cycle hY hc v 4 hdegree
  obtain ⟨q,rfl,hqx,hqr⟩ := hx
  obtain ⟨r,rfl,hrx,hrr⟩ := hy
  obtain ⟨i,rfl⟩ := e.surjective q
  obtain ⟨j,rfl⟩ := e.surjective r
  have hij : i≠j := fun hh => hxy (congrArg (fun i => (e i).val) hh)
  let b : Fin 4 → Bool := fun i => contactSectorTriangleFlag hY hc v (e i)
  have hcount : triangleFlagCount b=faceCornerCount (boundaryArray Y c hY hc 3) v :=
    (Equiv.sum_comp e (fun q => if contactSectorTriangleFlag hY hc v q then (1:ℕ) else 0)).trans
      (contactSectorTriangleFlag_vertex_count hY hc v)
  have hsi : sharedFourFlags b i=true := by
    change (b i && b (i+1))=true
    simp only [Bool.and_eq_true]
    refine ⟨hqr,?_⟩
    change contactSectorTriangleFlag hY hc v (e (i+1))=true
    rw [←he i,contactSectorTriangleFlag_rotate]
    exact hqx
  have hsj : sharedFourFlags b j=true := by
    change (b j && b (j+1))=true
    simp only [Bool.and_eq_true]
    refine ⟨hrr,?_⟩
    change contactSectorTriangleFlag hY hc v (e (j+1))=true
    rw [←he j,contactSectorTriangleFlag_rotate]
    exact hrx
  rcases (sharedFourFlags_exact b (hcount.trans_le ht)).2.2.2 i j hij hsi hsj with h | h
  · have hr := contactSectorTriangleFlag_contact hY hc hirr v (e i)
      (by rw [contactSectorTriangleFlag_rotate]; exact hqx)
    exact (congrArg (fun q : ContactNeighbor Y c v => inner ℝ (Y (e i)) (Y q))
      ((he i).trans (congrArg e h))).symm.trans hr
  · have hr := contactSectorTriangleFlag_contact hY hc hirr v (e j)
      (by rw [contactSectorTriangleFlag_rotate]; exact hrx)
    have hh : inner ℝ (Y (e j)) (Y (e i))=c :=
      (congrArg (fun q : ContactNeighbor Y c v => inner ℝ (Y (e j)) (Y q))
        ((he j).trans (congrArg e h))).symm.trans hr
    exact (real_inner_comm _ _).trans hh


theorem sharedTriangleGraph_degree_four_one_iff {Y : Fin 8 → Point} {c : ℝ}
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (v : Fin 8)
    (hdegree : Fintype.card (ContactNeighbor Y c v)=4)
    (ht : faceCornerCount (boundaryArray Y c hY hc 3) v≤3) :
    (sharedTriangleGraph hY hc).degree v=1 ↔
      faceCornerCount (boundaryArray Y c hY hc 3) v=2 ∧
      ∃ q : ContactNeighbor Y c v, contactSectorTriangleFlag hY hc v q=true ∧
        contactSectorTriangleFlag hY hc v (contactRotateAt Y c hY hc v q)=true := by
  have hh := sharedTriangleGraph_degree_four_cases hY hc v hdegree ht
  constructor
  · intro h1
    have ht2 : faceCornerCount (boundaryArray Y c hY hc 3) v=2 := by
      have h3 := hh.1
      have h0 := hh.2.2
      omega
    have hp : 0 < (sharedTriangleGraph hY hc).degree v := by omega
    obtain ⟨w,q,hqw,hflag,hrev⟩ :=
      ((sharedTriangleGraph hY hc).degree_pos_iff_exists_adj v).mp hp
    refine ⟨ht2,q,hrev,?_⟩
    rw [contactSectorTriangleFlag_rotate]
    exact hflag
  · rintro ⟨ht2,q,h1,h2⟩
    have hle := hh.2.1 (by omega)
    have hadj : (sharedTriangleGraph hY hc).Adj v q.val := by
      refine ⟨q,rfl,?_,h1⟩
      rwa [contactSectorTriangleFlag_rotate] at h2
    have hp := ((sharedTriangleGraph hY hc).degree_pos_iff_exists_adj v).mpr ⟨q.val,hadj⟩
    omega

theorem auxiliary_graphs_shared_triangle_degrees (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) :
    let S := sharedTriangleGraph hY hc
    let d := fun v => Fintype.card (ContactNeighbor Y c v)
    let t := faceCornerCount (boundaryArray Y c hY hc 3)
    (∀ v, S.degree v≤2 ∧ (S.degree v=2 ↔ d v=4 ∧ t v=3) ∧
      (d v=3 → S.degree v=0)) ∧
    (∀ v w, S.Adj v w → d v=4 ∧ d w=4) ∧
    (∀ v x y, x≠y → S.Adj v x → S.Adj v y → inner ℝ (Y x) (Y y)=c) := by
  dsimp only
  have ha := covering_no_rattlers Y c hY hc hcupper hirr hbound hne hsupport
  have hd (v : Fin 8) : Fintype.card (ContactNeighbor Y c v)=3 ∨
      Fintype.card (ContactNeighbor Y c v)=4 := by
    have hh := degree_degree_four Y c hY hc.1 hcupper hirr hbound v (ha v)
    rw [←contactNeighbor_card_eq] at hh
    omega
  have ht := (rhombus_angles_assemble Y c hY hc hcupper hirr hbound hne hsupport).1
  have hlocal (v : Fin 8) : (sharedTriangleGraph hY hc).degree v≤2 ∧
      ((sharedTriangleGraph hY hc).degree v=2 ↔
        Fintype.card (ContactNeighbor Y c v)=4 ∧ faceCornerCount (boundaryArray Y c hY hc 3) v=3) ∧
      (Fintype.card (ContactNeighbor Y c v)=3 → (sharedTriangleGraph hY hc).degree v=0) := by
    rcases hd v with h3 | h4
    · have hz := sharedTriangleGraph_degree_three_zero hY hc v h3 ((ht v).1 h3)
      simp [hz,h3]
    · have hh := sharedTriangleGraph_degree_four_cases hY hc v h4 ((ht v).2 h4)
      have htle : faceCornerCount (boundaryArray Y c hY hc 3) v≤3 := (ht v).2 h4
      constructor
      · by_cases ht3 : faceCornerCount (boundaryArray Y c hY hc 3) v=3
        · exact (hh.1.mpr ht3).le
        · have hh1 := hh.2.1 (by omega)
          omega
      · exact ⟨by simpa only [h4,true_and] using hh.1,by omega⟩
  have hadj (v w : Fin 8) (hvw : (sharedTriangleGraph hY hc).Adj v w) :
      Fintype.card (ContactNeighbor Y c v)=4 := by
    rcases hd v with h3 | h4
    · have hz := (hlocal v).2.2 h3
      have hp := ((sharedTriangleGraph hY hc).degree_pos_iff_exists_adj v).mpr ⟨w,hvw⟩
      omega
    · exact h4
  refine ⟨hlocal,?_,?_⟩
  · intro v w hvw
    exact ⟨hadj v w hvw,hadj w v ((sharedTriangleGraph hY hc).adj_symm hvw)⟩
  · intro v x y hxy hvx hvy
    exact sharedTriangleGraph_two_neighbors_contact hY hc hirr v x y (hadj v x hvx)
      ((ht v).2 (hadj v x hvx)) hxy hvx hvy

#print axioms sharedTriangleGraph_degree_four_one_iff
#print axioms auxiliary_graphs_shared_triangle_degrees

#print axioms contactTriangleFlag_closing_contact
#print axioms contactSectorTriangleFlag_contact
#print axioms sharedTriangleGraph_two_neighbors_contact

#print axioms sharedTriangleGraph_degree_sum
#print axioms contactRotateAt_fin_cycle
#print axioms sharedTriangleGraph_degree_three_zero
#print axioms sharedTriangleGraph_degree_four_cases

#print axioms contactTriangleFlag_weighted_sum
#print axioms contactTriangleFlag_vertex_count
#print axioms contactSectorTriangleFlag_vertex_count

#print axioms sharedFourFlags_exact
#print axioms sharedThreeFlags_zero
#print axioms contactTriangleFlag_next
#print axioms contactSectorTriangleFlag_rotate
end Blueprint.Thomson.Tail.Implementation
