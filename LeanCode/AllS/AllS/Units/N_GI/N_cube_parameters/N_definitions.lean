import AllS.Units.N_G.N_disphenoid

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

def cubeLower (c : ℝ) : ℝ := 2*c^2/(1+c)
def cubeUpper (c : ℝ) : ℝ := (1+c)/2

def CubeEquations (c : ℝ) (q : Fin 3 → ℝ) : Prop :=
  0<c ∧ (∀k,0<q k) ∧ (∑k,q k=1) ∧ c^2*(∑k,1/q k)=1

def CubeFeasible (c : ℝ) (q : Fin 3 → ℝ) : Prop :=
  CubeEquations c q ∧ ∀k,cubeLower c≤q k ∧ q k≤cubeUpper c

def cubeDual (c : ℝ) (q : Fin 3 → ℝ) (k : Fin 3) : ℝ := c^2/q k

def cubePairAxis : Fin 4 → Fin 4 → Fin 3 :=
  ![![0,0,1,2],![0,0,2,1],![1,2,0,0],![2,1,0,0]]

def cubeModelA (e : Fin 3 → Point) (q : Fin 3 → ℝ) (i : Fin 4) : Point :=
  ∑k,(cubeSign i k*Real.sqrt (q k)) • e k

def cubeModelB (e : Fin 3 → Point) (c : ℝ) (q : Fin 3 → ℝ) (i : Fin 4) : Point :=
  ∑k,(-c*cubeSign i k/Real.sqrt (q k)) • e k

end Blueprint.Thomson.Tail.Implementation
