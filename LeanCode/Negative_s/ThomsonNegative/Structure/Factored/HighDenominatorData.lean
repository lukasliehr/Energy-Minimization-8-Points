import ThomsonNegative.Structure.Factored.HighData
import ThomsonNegative.Structure.Factored.DenominatorData
namespace ThomsonNegative.Structure.Factored.HighDenData
open ThomsonNegative.Structure.Exact
noncomputable def node_0_0 : Nat := 0x3b0000e01000
noncomputable def node_0_1 : Nat := 0x8003b0000e02000
noncomputable def node_0_2 : Nat := 0x20008003b0000e03000
noncomputable def node_0_3 : Nat := 0x800040001ca01870001104000
noncomputable def node_0_4 : Nat := 0x400008000106c0179006a30001305000
noncomputable def node_0_5 : Nat := 0x8000004000001ff5e010561006e99005aa1800c8de015c490001908000
noncomputable def node_0_6 : Nat := 0x10000000200000004000f3007fd27001039e7001d743400516a2a0035591001c5eb3000d412c004c9dfb0001f0b000
noncomputable def node_0_7 : Nat := 0x8000000008000000007ffff0d008001116007ffb6e9007fd9df800821f26a00747b7d400a3f03ca003a21d1800d465c4900456020600922318d000240d000
noncomputable def node_0_8 : Nat := 0x400000000020000000001000000f3007ffffa4e003ffff32f802000b431800ffe5c8b5007fdae57c004147dd31001ccaaa0700148964c4d003fca38b600638b033780149da0a78011a1273ab000290f000
noncomputable def node_0_9 : Nat := 0x8000000000200000000007fffffc340200000c5700800009f7801fffa2b32008007f635c02002ffdbd007ea5958d0021eca248c00676fc0fac02c901dae1003c5a1923802e93f07a20062b6a4644021a1273ab0002a10000
noncomputable def node_0_10 : Nat := 0x2000000000080000000002000000f3007ffffcad801ffffe4790080017f2b001ffda525b007ffbf6c68020599a7890076f30c6a002810b20a100352f4a42803d799765300020a573b0035e647611005c3207798021a1273ab0002a11000
noncomputable def node_0_11 : Nat := 0x20000000000400000000007fffffe1a010000038f4020000071e803fff9e7cd008005754a200fffa9dd0401fd2b19c880429cd75e1006b582220e016b137de5c007e91d95b807cf7019670015389cdb6017b67160ac01ab5ad51d8041a1273ab0002b12000
noncomputable def node_0_12 : Nat := 0x80000000000800000000008000000f3007fffff0d00080000000000800062670007ffce3d7c00800413310008059443b0007d088bdb0008cf0c64da005ae73197000caf2a44e00012db3995000f25ab328c002bc288eb000a96e6adf00073ca336900081a1273ab0002c13000
noncomputable def node_0_13 : Nat := 0x80000000000400000000001ffffffe1a01000001023007fffff868003fffe76640020006fd1e800fff8d0a6c007fd5677b00040d42e180001e02f8b1ac01320994b6a0047fa46a48006e05daae400041010cd8801c6982a3dc00412a0f060004d690ddd8001e452185ca0101a1273ab0002d14000
noncomputable def node_0_14 : Nat := 0x2000000000008000000000020000000f3007fffffbba802000001f53008000185d0001fffc1f09c008002ab7a2002004e01b0c007f1685a580021338f2d2a006f838c35b002a215076da0035f748a400039796e44cc00167a170ba00344440c31c00532bf9a58002437b2b47b007c21f93ce80201a1273ab0002e15000
noncomputable def nodes_0 : Nat → Nat
 | 0 => node_0_0
 | 1 => node_0_1
 | 2 => node_0_2
 | 3 => node_0_3
 | 4 => node_0_4
 | 5 => node_0_5
 | 6 => node_0_6
 | 7 => node_0_7
 | 8 => node_0_8
 | 9 => node_0_9
 | 10 => node_0_10
 | 11 => node_0_11
 | 12 => node_0_12
 | 13 => node_0_13
 | 14 => node_0_14
 | _ => oneRecord
def factors_0 : Nat → Nat
 | 0 => 3
 | 1 => 3
 | 2 => 2
 | 3 => 2
 | 4 => 9
 | 5 => 9
 | 6 => 4
 | 7 => 4
 | 8 => 0
 | 9 => 0
 | 10 => 0
 | 11 => 0
 | 12 => 0
 | 13 => 0
 | _ => 0
noncomputable def chain_0 : ProductChain := ⟨14,nodes_0,fun k => DenData.factorWord (factors_0 k),151,21,46⟩
noncomputable def node_1_0 : Nat := 0x600301000
noncomputable def nodes_1 : Nat → Nat
 | 0 => node_1_0
 | _ => oneRecord
def factors_1 : Nat → Nat
 | _ => 0
noncomputable def chain_1 : ProductChain := ⟨0,nodes_1,fun k => DenData.factorWord (factors_1 k),9,1,3⟩
noncomputable def node_2_0 : Nat := 0xec00801000
noncomputable def nodes_2 : Nat → Nat
 | 0 => node_2_0
 | _ => oneRecord
def factors_2 : Nat → Nat
 | _ => 0
noncomputable def chain_2 : ProductChain := ⟨0,nodes_2,fun k => DenData.factorWord (factors_2 k),24,1,8⟩
noncomputable def node_3_0 : Nat := 0x1800501000
noncomputable def node_3_1 : Nat := 0x63800602000
noncomputable def nodes_3 : Nat → Nat
 | 0 => node_3_0
 | 1 => node_3_1
 | _ => oneRecord
def factors_3 : Nat → Nat
 | 0 => 1
 | _ => 0
noncomputable def chain_3 : ProductChain := ⟨1,nodes_3,fun k => DenData.factorWord (factors_3 k),21,2,6⟩
noncomputable def node_4_0 : Nat := 0x600301000
noncomputable def nodes_4 : Nat → Nat
 | 0 => node_4_0
 | _ => oneRecord
def factors_4 : Nat → Nat
 | _ => 0
noncomputable def chain_4 : ProductChain := ⟨0,nodes_4,fun k => DenData.factorWord (factors_4 k),9,1,3⟩
noncomputable def node_5_0 : Nat := 0x3800601000
noncomputable def node_5_1 : Nat := 0x7b89f83c8b4800c04000
noncomputable def node_5_2 : Nat := 0x200d87d0c242a84ec8347a8362c272d801207000
noncomputable def nodes_5 : Nat → Nat
 | 0 => node_5_0
 | 1 => node_5_1
 | 2 => node_5_2
 | _ => oneRecord
def factors_5 : Nat → Nat
 | 0 => 9
 | 1 => 9
 | _ => 0
noncomputable def chain_5 : ProductChain := ⟨2,nodes_5,fun k => DenData.factorWord (factors_5 k),62,7,18⟩
noncomputable def node_6_0 : Nat := 0x3b0000e01000
noncomputable def node_6_1 : Nat := 0x8003b0000e02000
noncomputable def node_6_2 : Nat := 0x20008003b0000e03000
noncomputable def node_6_3 : Nat := 0x800040001ca01870001104000
noncomputable def node_6_4 : Nat := 0x400008000106c0179006a30001305000
noncomputable def node_6_5 : Nat := 0x1000002000003fe50080d801187800bf6007ca50001707000
noncomputable def node_6_6 : Nat := 0x800000080000008001b0080036007f4ed0080d140094085002fa5600d72d30001c09000
noncomputable def node_6_7 : Nat := 0x2000000100000007fff2803fff94020169200fe7d90076647805918bc00b0f0601572d30001d0a000
noncomputable def node_6_8 : Nat := 0x20000000800000020001b0080000001ff49c00808dc00211b4a00621980030beac004052c002572d30001e0b000
noncomputable def node_6_9 : Nat := 0x8000000100000001ffff28040001b008016c800ff44b001f8413004894ea004f8f680182a7f001550ee804572d30001f0c000
noncomputable def node_6_10 : Nat := 0x400000008000000100006c01fffe5003ff4b7008074700103241801b399e0060cd36000e3b7001d8207c0129785004572d30001f0d000
noncomputable def node_6_11 : Nat := 0x80000000800000007fffe50080005100800b13007fba7f007f7132008a55ca0055a60600d9af7e0011159900d0d915005fbc37008572d3000200e000
noncomputable def node_6_12 : Nat := 0x4000000020000000100001b007fffca003ffd4f80200a1280100494d007a8db4004d2bf1000f7ed1001c899e500201e42005c4737801b492c8010572d3000210f000
noncomputable def nodes_6 : Nat → Nat
 | 0 => node_6_0
 | 1 => node_6_1
 | 2 => node_6_2
 | 3 => node_6_3
 | 4 => node_6_4
 | 5 => node_6_5
 | 6 => node_6_6
 | 7 => node_6_7
 | 8 => node_6_8
 | 9 => node_6_9
 | 10 => node_6_10
 | 11 => node_6_11
 | 12 => node_6_12
 | _ => oneRecord
def factors_6 : Nat → Nat
 | 0 => 3
 | 1 => 3
 | 2 => 2
 | 3 => 2
 | 4 => 4
 | 5 => 4
 | 6 => 0
 | 7 => 0
 | 8 => 0
 | 9 => 0
 | 10 => 0
 | 11 => 0
 | _ => 0
noncomputable def chain_6 : ProductChain := ⟨12,nodes_6,fun k => DenData.factorWord (factors_6 k),110,15,33⟩
noncomputable def chain : Nat → ProductChain
 | 0 => chain_0
 | 1 => chain_1
 | 2 => chain_2
 | 3 => chain_3
 | 4 => chain_4
 | 5 => chain_5
 | 6 => chain_6
 | _ => chain_0
noncomputable def unit : Nat → Nat
 | 0 => 6912
 | 1 => 2
 | 2 => 108
 | 3 => 8
 | 4 => 2
 | 5 => 24
 | 6 => 6912
 | _ => 6912
noncomputable def denominatorWord : Nat → Nat
 | 0 => HighData.A_den
 | 1 => HighData.K3_den
 | 2 => HighData.K14_den
 | 3 => HighData.K15_den
 | 4 => HighData.K36_den
 | 5 => HighData.H3_den
 | 6 => HighData.H14_den
 | _ => HighData.A_den
noncomputable def factorIndex : Nat → Nat → Nat
 | 0 => factors_0
 | 1 => factors_1
 | 2 => factors_2
 | 3 => factors_3
 | 4 => factors_4
 | 5 => factors_5
 | 6 => factors_6
 | _ => factors_0
end ThomsonNegative.Structure.Factored.HighDenData
