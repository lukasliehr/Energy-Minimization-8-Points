import Mathlib.Data.Rat.Defs

/- Exact untrusted source literals. No acceptance or numerical conclusion is
   attached to these records. Flattened lower triangles are row major. -/
namespace Blueprint.CAP.Literals

inductive Contact where
  | A | B | C | D
  deriving DecidableEq

inductive Profile where
  | original | far4 | far6 | general
  deriving DecidableEq

inductive Balance where
  | unit | riesz
  deriving DecidableEq

structure Block where
  name : String
  order : Nat
  diagonalExponents : List Int
  strictLower : List Int
  factors : List (List Int)

def Block.Shape (b : Block) (degree : Nat) : Prop :=
  b.diagonalExponents.length = b.order ∧
  b.strictLower.length = b.order * (b.order - 1) / 2 ∧
  b.factors.length = degree + 1 ∧
  ∀ f ∈ b.factors, f.length = b.order * (b.order + 1) / 2

structure Cell where
  id : String
  degree : Nat
  center : Rat
  halfwidth : Rat
  validationOrder : Nat
  bernsteinDegree : Nat
  profile : Profile
  balance : Balance
  factorBits : Nat
  metricBits : Nat
  floorExponent : Int
  momentPivots : List Nat
  auxiliaryNodes : List Contact
  rootCoefficients : List Int
  jointDepth : Nat
  jointExactBlocks : List String
  blocks : List Block

def Cell.Shape (c : Cell) : Prop :=
  c.rootCoefficients.length = c.validationOrder + 1 ∧
  c.momentPivots.length = c.degree / 2 ∧
  ∀ b ∈ c.blocks, b.Shape c.bernsteinDegree

end Blueprint.CAP.Literals
