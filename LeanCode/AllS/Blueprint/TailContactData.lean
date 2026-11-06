import Blueprint.TailLocalCoordinates

noncomputable section
namespace Blueprint.Thomson.Tail

/-- Cyclic contacts: shift one joins the layers; shift two lies within a layer. -/
abbrev ContactIndex := Fin 8 × Fin 2

def contactNext (e : ContactIndex) : Fin 8 := e.1 + if e.2=0 then 1 else 2

def contactPair (e : ContactIndex) : Fin 8 × Fin 8 :=
  (min e.1 (contactNext e),max e.1 (contactNext e))

def cyclicContactPairs : Finset (Fin 8 × Fin 8) := Finset.univ.image contactPair

def IsCyclicContact (i j : Fin 8) : Prop := j=i+1 ∨ j=i+2 ∨ i=j+1 ∨ i=j+2
instance (i j : Fin 8) : Decidable (IsCyclicContact i j) := by unfold IsCyclicContact; infer_instance

def contactKappa : ℝ := 1+1/Real.sqrt 2

def contactWeight (e : ContactIndex) : ℝ := if e.2=0 then 1 else contactKappa

def contactTotalWeight : ℝ := 16+4*Real.sqrt 2

end Blueprint.Thomson.Tail
