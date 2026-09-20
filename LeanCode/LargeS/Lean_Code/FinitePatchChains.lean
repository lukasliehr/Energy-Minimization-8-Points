import Lean_Code.SphericalLocalConnectivity

set_option maxHeartbeats 1000000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
universe u

/-- A finite chain whose links have both endpoints in a named patch. Later,
the patches will be compact local convex neighborhoods in the face. -/
inductive PatchArcChain {ι : Type u} (patch : ι → Set ℝ³) (a : ℝ³) : ℝ³ → Type u
  | point (ha : ‖a‖ = 1) : PatchArcChain patch a a
  | tail {b : ℝ³} (p : PatchArcChain patch a b) (i : ι) (z : ℝ³)
      (hb : b ∈ patch i) (hz : z ∈ patch i) : PatchArcChain patch a z

namespace PatchArcChain

variable {ι : Type*} {patch : ι → Set ℝ³} {a b : ℝ³}

def labels : {b : ℝ³} → PatchArcChain patch a b → List ι
  | _, .point _ => []
  | _, .tail p i _ _ _ => i :: p.labels

def length : {b : ℝ³} → PatchArcChain patch a b → ℝ
  | _, .point _ => 0
  | _, .tail (b := y) p _ z _ _ => p.length + sphereAngle y z

lemma endpoint_unit (hpatch : ∀ i x, x ∈ patch i → ‖x‖ = 1)
    (p : PatchArcChain patch a b) : ‖b‖ = 1 := by
  cases p with
  | point ha => exact ha
  | tail => apply hpatch; assumption

lemma length_nonneg (p : PatchArcChain patch a b) : 0 ≤ p.length := by
  induction p with
  | point => exact le_rfl
  | @tail b p i z hb hz ih => exact add_nonneg ih (sphereAngle_range b z).1

/-- Truncating at a previous visit to a patch never increases the angular
distance estimate to an arbitrary final unit point. -/
lemma truncate_at_label (hpatch : ∀ i x, x ∈ patch i → ‖x‖ = 1)
    (p : PatchArcChain patch a b) (hnodup : p.labels.Nodup)
    (i : ι) (hi : i ∈ p.labels) (z : ℝ³) (hz : ‖z‖ = 1) :
    ∃ u, ∃ q : PatchArcChain patch a u, q.labels.Nodup ∧ i ∉ q.labels ∧ u ∈ patch i ∧
      q.length + sphereAngle u z ≤ p.length + sphereAngle b z := by
  induction p with
  | point ha => simp [labels] at hi
  | @tail b p j y hb hy ih =>
    have hnodup' : j ∉ p.labels ∧ p.labels.Nodup := List.nodup_cons.mp hnodup
    by_cases hij : i = j
    · subst j
      refine ⟨b, p, hnodup'.2, hnodup'.1, hb, ?_⟩
      have htri := sphereAngle_triangle b y z (p.endpoint_unit hpatch) (hpatch i y hy) hz
      change p.length + sphereAngle b z ≤ p.length + sphereAngle b y + sphereAngle y z
      linarith
    · have hip : i ∈ p.labels := (List.mem_cons.mp hi).resolve_left hij
      obtain ⟨u, q, hq, hiq, hui, hlen⟩ := ih hnodup'.2 hip
      refine ⟨u, q, hq, hiq, hui, ?_⟩
      have htri := sphereAngle_triangle b y z (p.endpoint_unit hpatch) (hpatch j y hy) hz
      change q.length + sphereAngle u z ≤ p.length + sphereAngle b y + sphereAngle y z
      linarith

/-- Remove repeated patch visits by shortcuts. This provides a uniform finite
bound on the number of links before the compact minimization step. -/
theorem compress (hpatch : ∀ i x, x ∈ patch i → ‖x‖ = 1)
    (p : PatchArcChain patch a b) :
    ∃ q : PatchArcChain patch a b, q.labels.Nodup ∧ q.length ≤ p.length := by
  classical
  induction p with
  | point ha => exact ⟨.point ha, by simp [labels], le_rfl⟩
  | @tail b p i z hb hz ih =>
    obtain ⟨q, hq, hlen⟩ := ih
    by_cases hi : i ∈ q.labels
    · obtain ⟨u, r, hr, hir, hui, hshort⟩ :=
        q.truncate_at_label hpatch hq i hi z (hpatch i z hz)
      refine ⟨.tail r i z hui hz, List.nodup_cons.mpr ⟨hir, hr⟩, ?_⟩
      change r.length + sphereAngle u z ≤ p.length + sphereAngle b z
      linarith
    · refine ⟨.tail q i z hb hz, List.nodup_cons.mpr ⟨hi, hq⟩, ?_⟩
      change q.length + sphereAngle b z ≤ p.length + sphereAngle b z
      linarith

theorem compressed_link_bound [Fintype ι] (hpatch : ∀ i x, x ∈ patch i → ‖x‖ = 1)
    (p : PatchArcChain patch a b) :
    ∃ q : PatchArcChain patch a b,
      q.labels.length ≤ Fintype.card ι ∧ q.length ≤ p.length := by
  classical
  obtain ⟨q, hq, hlen⟩ := p.compress hpatch
  refine ⟨q, ?_, hlen⟩
  have hcard := Finset.card_le_univ q.labels.toFinset
  simpa only [List.toFinset_card_of_nodup hq] using hcard

end PatchArcChain
end SquareAntiprismVerification
