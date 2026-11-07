import AllS.Units.N_GI.N_incident_bound.N_noncontacts
import AllS.Units.N_GI.N_incident_bound.N_contact_terms

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

def contactNeighbors (i : Fin 8) : Finset (Fin 8) :=
  Finset.univ.filter (fun j=>i≠j ∧ IsCyclicContact i j)
def contactOther (i : Fin 8) (e : ContactIndex) : Fin 8 :=
  if e.1=i then contactNext e else e.1

theorem contactOther_combinatorics : ∀ i : Fin 8,
    (contactIncident i).image (contactOther i)=contactNeighbors i ∧
    ∀ e∈contactIncident i, ∀ f∈contactIncident i, contactOther i e=contactOther i f → e=f := by decide

theorem neighbor_partition : ∀ i : Fin 8,
    Disjoint (contactNeighbors i) (noncontactNeighbors i) ∧
      contactNeighbors i∪noncontactNeighbors i=Finset.univ.erase i := by decide

theorem contactOther_distance (Y : Fin 8→Point) (i : Fin 8) (e : ContactIndex)
    (he : e∈contactIncident i) :
    squaredDistance Y i (contactOther i e)=squaredDistance Y e.1 (contactNext e) := by
  have he' : e.1=i ∨ contactNext e=i := (Finset.mem_filter.mp he).2
  unfold contactOther
  by_cases hi : e.1=i
  · rw [if_pos hi,hi]
  · rw [if_neg hi,he'.resolve_left hi,squaredDistance_symm]

theorem incident_contact_reindex (p : ℝ) (q : TangentCoordinates) (i : Fin 8) :
    (∑ j∈contactNeighbors i, (tau/squaredDistance (orthographicChart q) i j)^(p+1))=
      ∑ e∈contactIncident i, (tau/squaredDistance (orthographicChart q) e.1 (contactNext e))^(p+1) := by
  rw [←(contactOther_combinatorics i).1,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro e he
    rw [contactOther_distance _ i e he]
  · exact (contactOther_combinatorics i).2

theorem incident_bound_all_incident (p : ℝ) (hp : (97:ℝ)/2≤p) (q : TangentCoordinates)
    (hq : q∈convexTailDomain p) (i : Fin 8) :
    (∑ j∈Finset.univ.erase i, (tau/squaredDistance (orthographicChart q) i j)^(p+1))<(31:ℝ)/5 := by
  rw [←(neighbor_partition i).2,Finset.sum_union (neighbor_partition i).1,incident_contact_reindex]
  have h1 := incident_contact_sum_upper p hp q hq i
  have h2 := (incident_bound_noncontacts p hp q hq).2 i
  exact (add_lt_add h1 h2).trans (incident_total_scalar p hp)

#print axioms incident_bound_all_incident
end Blueprint.Thomson.Tail.Implementation
