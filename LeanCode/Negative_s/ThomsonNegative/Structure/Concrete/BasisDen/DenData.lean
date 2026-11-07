import ThomsonNegative.Structure.Concrete.BasisData
import ThomsonNegative.Structure.Factored.DenominatorData
namespace ThomsonNegative.Structure.Concrete.BasisDen.DenData
open ThomsonNegative.Structure.Exact
noncomputable def node0_0 : Nat := 0x3000601000
noncomputable def nodes0 : Nat → Nat
 | 0 => node0_0
 | _ => oneRecord
def factors0 : Nat → Nat
 | _ => 0
noncomputable def chain0 : ProductChain := ⟨0,nodes0,fun k => ThomsonNegative.Structure.Factored.DenData.factorWord (factors0 k),18,1,6⟩
noncomputable def node1_0 : Nat := 0x600301000
noncomputable def node1_1 : Nat := 0x7aaa26c600804000
noncomputable def nodes1 : Nat → Nat
 | 0 => node1_0
 | 1 => node1_1
 | _ => oneRecord
def factors1 : Nat → Nat
 | 0 => 9
 | _ => 0
noncomputable def chain1 : ProductChain := ⟨1,nodes1,fun k => ThomsonNegative.Structure.Factored.DenData.factorWord (factors1 k),30,4,8⟩
noncomputable def node2_0 : Nat := 0x600301000
noncomputable def node2_1 : Nat := 0x7e923ac600804000
noncomputable def nodes2 : Nat → Nat
 | 0 => node2_0
 | 1 => node2_1
 | _ => oneRecord
def factors2 : Nat → Nat
 | 0 => 10
 | _ => 0
noncomputable def chain2 : ProductChain := ⟨1,nodes2,fun k => ThomsonNegative.Structure.Factored.DenData.factorWord (factors2 k),30,4,8⟩
noncomputable def node3_0 : Nat := 0x600301000
noncomputable def node3_1 : Nat := 0x8644c600803000
noncomputable def nodes3 : Nat → Nat
 | 0 => node3_0
 | 1 => node3_1
 | _ => oneRecord
def factors3 : Nat → Nat
 | 0 => 8
 | _ => 0
noncomputable def chain3 : ProductChain := ⟨1,nodes3,fun k => ThomsonNegative.Structure.Factored.DenData.factorWord (factors3 k),28,3,8⟩
noncomputable def node4_0 : Nat := 0x600301000
noncomputable def node4_1 : Nat := 0x8644c600803000
noncomputable def nodes4 : Nat → Nat
 | 0 => node4_0
 | 1 => node4_1
 | _ => oneRecord
def factors4 : Nat → Nat
 | 0 => 8
 | _ => 0
noncomputable def chain4 : ProductChain := ⟨1,nodes4,fun k => ThomsonNegative.Structure.Factored.DenData.factorWord (factors4 k),28,3,8⟩
noncomputable def node5_0 : Nat := 0x1a00501000
noncomputable def node5_1 : Nat := 0x12be4a00703000
noncomputable def nodes5 : Nat → Nat
 | 0 => node5_0
 | 1 => node5_1
 | _ => oneRecord
def factors5 : Nat → Nat
 | 0 => 7
 | _ => 0
noncomputable def chain5 : ProductChain := ⟨1,nodes5,fun k => ThomsonNegative.Structure.Factored.DenData.factorWord (factors5 k),25,3,7⟩
noncomputable def node6_0 : Nat := 0x3000601000
noncomputable def node6_1 : Nat := 0x83000602000
noncomputable def node6_2 : Nat := 0x8070d000803000
noncomputable def node6_3 : Nat := 0x8008108104b0f3000c05000
noncomputable def node6_4 : Nat := 0x2000ff08004d80b0173000d06000
noncomputable def node6_5 : Nat := 0x20008041ff07282de0394273000e07000
noncomputable def nodes6 : Nat → Nat
 | 0 => node6_0
 | 1 => node6_1
 | 2 => node6_2
 | 3 => node6_3
 | 4 => node6_4
 | 5 => node6_5
 | _ => oneRecord
def factors6 : Nat → Nat
 | 0 => 3
 | 1 => 2
 | 2 => 4
 | 3 => 0
 | 4 => 0
 | _ => 0
noncomputable def chain6 : ProductChain := ⟨5,nodes6,fun k => ThomsonNegative.Structure.Factored.DenData.factorWord (factors6 k),50,7,14⟩
noncomputable def node7_0 : Nat := 0x19000901000
noncomputable def node7_1 : Nat := 0x2019000902000
noncomputable def node7_2 : Nat := 0x1001b86d000b03000
noncomputable def node7_3 : Nat := 0x801240506d000b04000
noncomputable def node7_4 : Nat := 0x800770bf01d0ad000c05000
noncomputable def node7_5 : Nat := 0x20010905c06880e012d000d06000
noncomputable def nodes7 : Nat → Nat
 | 0 => node7_0
 | 1 => node7_1
 | 2 => node7_2
 | 3 => node7_3
 | 4 => node7_4
 | 5 => node7_5
 | _ => oneRecord
def factors7 : Nat → Nat
 | 0 => 3
 | 1 => 2
 | 2 => 0
 | 3 => 0
 | 4 => 0
 | _ => 0
noncomputable def chain7 : ProductChain := ⟨5,nodes7,fun k => ThomsonNegative.Structure.Factored.DenData.factorWord (factors7 k),46,6,13⟩
noncomputable def chain : Nat → ProductChain
 | 0 => chain0
 | 1 => chain1
 | 2 => chain2
 | 3 => chain3
 | 4 => chain4
 | 5 => chain5
 | 6 => chain6
 | 7 => chain7
 | _ => chain0
noncomputable def unit : Nat → Nat
 | 0 => 16
 | 1 => 2
 | 2 => 2
 | 3 => 2
 | 4 => 2
 | 5 => 10
 | 6 => 16
 | 7 => 144
 | _ => 16
noncomputable def word : Nat → Nat
 | 0 => ThomsonNegative.Structure.Concrete.BasisData.denominator 0
 | 1 => ThomsonNegative.Structure.Concrete.BasisData.denominator 1
 | 2 => ThomsonNegative.Structure.Concrete.BasisData.denominator 2
 | 3 => ThomsonNegative.Structure.Concrete.BasisData.denominator 3
 | 4 => ThomsonNegative.Structure.Concrete.BasisData.denominator 4
 | 5 => ThomsonNegative.Structure.Concrete.BasisData.denominator 5
 | 6 => ThomsonNegative.Structure.Concrete.BasisData.denominator 6
 | 7 => ThomsonNegative.Structure.Concrete.BasisData.denominator 7
 | _ => ThomsonNegative.Structure.Concrete.BasisData.denominator 0
noncomputable def factorIndex : Nat → Nat → Nat
 | 0 => factors0
 | 1 => factors1
 | 2 => factors2
 | 3 => factors3
 | 4 => factors4
 | 5 => factors5
 | 6 => factors6
 | 7 => factors7
 | _ => factors0
end ThomsonNegative.Structure.Concrete.BasisDen.DenData
