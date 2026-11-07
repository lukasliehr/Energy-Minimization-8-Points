import AllS.Units.N_GI.N_cycle5.N_jensen

noncomputable section
open Real
open scoped BigOperators
namespace Blueprint.Thomson.Tail.Implementation

theorem force_cost_jensen {n : ℕ} (hn : 2 ≤ n) (k₀ : Fin n) (α c : Fin n → ℝ)
    (v K total : ℝ) (f : ℝ → ℝ)
    (hα : ∀ i, α i ∈ Set.Ioo (0:ℝ) π) (ha₀ : α k₀=2*v) (hc₀ : c k₀=1)
    (hsum : ∑ i,α i=total) (hK : 0 ≤ K)
    (hf : ConvexOn ℝ (Set.Ioo (0:ℝ) (π/2)) f)
    (hcost : ∀ i, K*f (α i/2) ≤ c i) :
    1+K*(n-1:ℕ)*f ((total/2-v)/(n-1:ℕ)) ≤ ∑ i,c i := by
  let S := Finset.univ.erase k₀
  have hcard : S.card=n-1 := by simp [S]
  have hS : S.Nonempty := Finset.card_pos.mp (by rw [hcard]; omega)
  have hrem : ∑ i ∈ S,α i/2=total/2-v := by
    have h := Finset.sum_erase_add (Finset.univ (α:=Fin n)) (fun i => α i/2) (Finset.mem_univ k₀)
    simp only [← Finset.sum_div] at h ⊢
    rw [hsum,ha₀] at h
    dsimp [S]
    linarith
  have hJ := force_jensen S hS (fun i => α i/2)
    (fun i _ => ⟨by linarith [(hα i).1],by linarith [(hα i).2]⟩) f hf
  rw [hcard,hrem] at hJ
  have hJK := mul_le_mul_of_nonneg_left hJ hK
  have hcostsum : K*(∑ i ∈ S,f (α i/2)) ≤ ∑ i ∈ S,c i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hcost i)
  have hc := Finset.sum_erase_add (Finset.univ (α:=Fin n)) c (Finset.mem_univ k₀)
  rw [hc₀] at hc
  change (∑ i ∈ S,c i)+1=∑ i,c i at hc
  linarith

def cycleNormalizedCost (m : ℝ) (Y : Fin 8 → Point) (u : Point) (C : FlowCycle) : ℝ :=
  ∑ i,normalizedEdgeCost m u Y (C.point i) (C.point (i+1))

theorem positive_cycle_jensen (Y : Fin 8 → Point) (p m : ℝ) (i₀ j₀ : Fin 8)
    (hY : IsConfiguration Y) (hp : 0 < p) (hstat : Stationary p Y) (hne : i₀ ≠ j₀)
    (hm : 0 < m) (hmmax : m ≤ 29/20) (hd : squaredDistance Y i₀ j₀=m)
    (hmin : ∀ i j, i ≠ j → m ≤ squaredDistance Y i j)
    (C : FlowCycle) (hC : C.Positive (forceFlow p (forceAxis Y i₀ j₀ m) Y))
    (k₀ : Fin (C.size+1)) (hk₀ : C.point k₀=i₀) (hk₁ : C.point (k₀+1)=j₀)
    (q : ℤ) (hsum : ∑ i,cycleProjectedAngle Y (forceAxis Y i₀ j₀ m) C i=2*π*q) :
    let v := forceAngle m/2
    let u := forceAxis Y i₀ j₀ m
    1+(tan v)⁻¹*(C.size:ℝ)*tan ((π*q-v)/C.size) ≤ cycleNormalizedCost m Y u C ∧
    1+tan v*(C.size:ℝ)*(tan ((π*q-v)/C.size))⁻¹ ≤ cycleNormalizedCost m Y u C := by
  let u := forceAxis Y i₀ j₀ m
  let v := forceAngle m/2
  let α := cycleProjectedAngle Y u C
  let c := fun i => normalizedEdgeCost m u Y (C.point i) (C.point (i+1))
  have he := edge_cost Y p m i₀ j₀ hY hp hstat hne hm hmmax hd hmin
  have ha (i : Fin (C.size+1)) : α i ∈ Set.Ioo (0:ℝ) π :=
    ⟨(he.1 _ _ (hC i)).2.2.1,(he.1 _ _ (hC i)).2.2.2.1⟩
  have hα₀ : α k₀=2*v := by
    dsimp [α,cycleProjectedAngle,u,v]
    rw [hk₀,hk₁,closest_projection_angle Y hY m i₀ j₀ hd]
    ring
  have hc₀ : c k₀=1 := by dsimp [c]; rw [hk₀,hk₁]; exact he.2.1
  have ht : 0 < tan v := (force_half_angle_ratios m hm hmmax).1
  have hlen := C.length_ge
  have htbound (i : Fin (C.size+1)) : (tan v)⁻¹*tan (α i/2) ≤ c i :=
    (le_max_left _ _).trans (he.1 _ _ (hC i)).2.2.2.2.2.2.2
  have hcbound (i : Fin (C.size+1)) : tan v*(tan (α i/2))⁻¹ ≤ c i :=
    (le_max_right _ _).trans (he.1 _ _ (hC i)).2.2.2.2.2.2.2
  have htJ := force_cost_jensen (by omega : 2 ≤ C.size+1) k₀ α c v (tan v)⁻¹ (2*π*q)
    tan ha hα₀ hc₀ hsum (inv_pos.mpr ht).le force_convex_tan htbound
  have hcJ := force_cost_jensen (by omega : 2 ≤ C.size+1) k₀ α c v (tan v) (2*π*q)
    (fun x => (tan x)⁻¹) ha hα₀ hc₀ hsum ht.le force_convex_cot hcbound
  have hq : 2*π*(q:ℝ)/2=π*q := by ring
  simpa only [Nat.add_sub_cancel,hq,cycleNormalizedCost,c,u,v] using And.intro htJ hcJ

#print axioms positive_cycle_jensen
end Blueprint.Thomson.Tail.Implementation
