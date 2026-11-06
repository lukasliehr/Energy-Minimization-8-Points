import AllS.Units.N_AI.N_data.ScalarGates

namespace Blueprint.CAP
open scoped BigOperators

def QInterval.point (q : ℚ) : QInterval := ⟨q,q⟩
def QInterval.add (I J : QInterval) : QInterval := ⟨I.lo+J.lo,I.hi+J.hi⟩
def QInterval.neg (I : QInterval) : QInterval := ⟨-I.hi,-I.lo⟩
def QInterval.scale (q : ℚ) (I : QInterval) : QInterval :=
  ⟨min (q*I.lo) (q*I.hi),max (q*I.lo) (q*I.hi)⟩
def QInterval.mul (I J : QInterval) : QInterval :=
  ⟨min (min (I.lo*J.lo) (I.lo*J.hi)) (min (I.hi*J.lo) (I.hi*J.hi)),
   max (max (I.lo*J.lo) (I.lo*J.hi)) (max (I.hi*J.lo) (I.hi*J.hi))⟩
def QInterval.inv (I : QInterval) : QInterval := ⟨1/I.hi,1/I.lo⟩
def QInterval.sum {α : Type*} [Fintype α] (I : α → QInterval) : QInterval :=
  ⟨∑ i, (I i).lo, ∑ i, (I i).hi⟩
def QInterval.SubsetGate (I J : QInterval) : Prop := J.lo ≤ I.lo ∧ I.hi ≤ J.hi

end Blueprint.CAP
