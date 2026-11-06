import ThomsonNegative.Structure.Packed.IdentityKernel
namespace ThomsonNegative.Certificate.Bridges.RFChecks
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
noncomputable def e40n_left_0 : Nat := 0x800007ff8f49a96b5bffe0e73cfcb48fc0200ab5aed9685e0001063ab8ebd830000008cabe0f48800000005c1887b40000000003b142a0000000000014110000000000000004508000
noncomputable def e40n_left : Nat → Nat
  | 0 => e40n_left_0
  | _ => 0
noncomputable def e40n_right_0 : Nat := 0x300201000
noncomputable def e40n_right : Nat → Nat
  | 0 => e40n_right_0
  | _ => 0
noncomputable def e40n_scale : Nat := 0x798000000000000000004b01000
noncomputable def e40n_target0 : Nat := 0x800007ff8f49a96b5801fff0739e7e5a47e0000802ad6bb65a1780000020c7571d7b06000000008cabe0f4880000000002e0c43da000000000000ec50a800000000000002822000000000000000004e08000
noncomputable def e40n_target1 : Nat := 0x3cc0000000000000004201000
noncomputable def e40n_target2 : Nat := 0x300201000
noncomputable def e40n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 243
  maxLength := 8
  maxWidth := 78
  terms := 1
  left := e40n_left
  right := e40n_right
  scale := e40n_scale
  target0 := e40n_target0
  target1 := e40n_target1
  target2 := e40n_target2

theorem e40n_ok : e40n.check=true := by decide +kernel
noncomputable def e40d_left_0 : Nat := 0x7ff3943c72685b806c506d541600891ac7608d00008ecf3ed4000000488f050000000044b60000000000f300000000000003807000
noncomputable def e40d_left : Nat → Nat
  | 0 => e40d_left_0
  | _ => 0
noncomputable def e40d_right_0 : Nat := 0x300201000
noncomputable def e40d_right : Nat → Nat
  | 0 => e40d_right_0
  | _ => 0
noncomputable def e40d_scale : Nat := 0x180000000000000003d01000
noncomputable def e40d_target0 : Nat := 0xffe72878e4d0b600201b141b550580000448d63b04680000008ecf3ed4000000000911e0a0000000000112d80000000000007980000000000000004307000
noncomputable def e40d_target1 : Nat := 0x300000000000003201000
noncomputable def e40d_target2 : Nat := 0x300201000
noncomputable def e40d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 209
  maxLength := 7
  maxWidth := 67
  terms := 1
  left := e40d_left
  right := e40d_right
  scale := e40d_scale
  target0 := e40d_target0
  target1 := e40d_target1
  target2 := e40d_target2

theorem e40d_ok : e40d.check=true := by decide +kernel
noncomputable def e41n_left_0 : Nat := 0x7fffc636056dfc002fffc591443b9a7402016469cfa9c680004228793d6290000009174b44e600000001883639c0000000003aa5f8000000000003930000000000000004308000
noncomputable def e41n_left : Nat → Nat
  | 0 => e41n_left_0
  | _ => 0
noncomputable def e41n_right_0 : Nat := 0x300201000
noncomputable def e41n_right : Nat → Nat
  | 0 => e41n_right_0
  | _ => 0
noncomputable def e41n_scale : Nat := 0x798000000000000000004b01000
noncomputable def e41n_target0 : Nat := 0x7fffc636056dfc002001fff8b22887734e8000080591a73ea71a00000021143c9eb148000000009174b44e600000000003106c738000000000000ea97e000000000000001c98000000000000000004e08000
noncomputable def e41n_target1 : Nat := 0xf30000000000000004001000
noncomputable def e41n_target2 : Nat := 0x300201000
noncomputable def e41n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 243
  maxLength := 8
  maxWidth := 78
  terms := 1
  left := e41n_left
  right := e41n_right
  scale := e41n_scale
  target0 := e41n_target0
  target1 := e41n_target1
  target2 := e41n_target2

theorem e41n_ok : e41n.check=true := by decide +kernel
noncomputable def e41d_left_0 : Nat := 0x7ff3943c72685b806c506d541600891ac7608d00008ecf3ed4000000488f050000000044b60000000000f300000000000003807000
noncomputable def e41d_left : Nat → Nat
  | 0 => e41d_left_0
  | _ => 0
noncomputable def e41d_right_0 : Nat := 0x300201000
noncomputable def e41d_right : Nat → Nat
  | 0 => e41d_right_0
  | _ => 0
noncomputable def e41d_scale : Nat := 0x180000000000000003d01000
noncomputable def e41d_target0 : Nat := 0xffe72878e4d0b600201b141b550580000448d63b04680000008ecf3ed4000000000911e0a0000000000112d80000000000007980000000000000004307000
noncomputable def e41d_target1 : Nat := 0x300000000000003201000
noncomputable def e41d_target2 : Nat := 0x300201000
noncomputable def e41d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 209
  maxLength := 7
  maxWidth := 67
  terms := 1
  left := e41d_left
  right := e41d_right
  scale := e41d_scale
  target0 := e41d_target0
  target1 := e41d_target1
  target2 := e41d_target2

theorem e41d_ok : e41d.check=true := by decide +kernel
noncomputable def e42n_left_0 : Nat := 0xffffddd98fa712ee477d8000d4341ae4cda93c004003a3a344fc93f3000020036d9f61f881000000101a756e75a4e0000000085426bb464000000000048489f4300000000000031e647000000000000001dfdd000000000000000005109000
noncomputable def e42n_left : Nat → Nat
  | 0 => e42n_left_0
  | _ => 0
noncomputable def e42n_right_0 : Nat := 0x300201000
noncomputable def e42n_right : Nat → Nat
  | 0 => e42n_right_0
  | _ => 0
noncomputable def e42n_scale : Nat := 0xf3000000000000000000005401000
noncomputable def e42n_target0 : Nat := 0xffffddd98fa712ee477d008000d4341ae4cda93c00004003a3a344fc93f300000020036d9f61f88100000000101a756e75a4e000000000085426bb46400000000000048489f430000000000000031e64700000000000000001dfdd00000000000000000005909000
noncomputable def e42n_target1 : Nat := 0xf30000000000000000004c01000
noncomputable def e42n_target2 : Nat := 0x300201000
noncomputable def e42n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 276
  maxLength := 9
  maxWidth := 89
  terms := 1
  left := e42n_left
  right := e42n_right
  scale := e42n_scale
  target0 := e42n_target0
  target1 := e42n_target1
  target2 := e42n_target2

theorem e42n_ok : e42n.check=true := by decide +kernel
noncomputable def e42d_left_0 : Nat := 0x7ff3943c72685b806c506d541600891ac7608d00008ecf3ed4000000488f050000000044b60000000000f300000000000003807000
noncomputable def e42d_left : Nat → Nat
  | 0 => e42d_left_0
  | _ => 0
noncomputable def e42d_right_0 : Nat := 0x300201000
noncomputable def e42d_right : Nat → Nat
  | 0 => e42d_right_0
  | _ => 0
noncomputable def e42d_scale : Nat := 0x300000000000000003e01000
noncomputable def e42d_target0 : Nat := 0x7ff3943c72685b000806c506d541600000891ac7608d00000008ecf3ed4000000000488f050000000000044b60000000000000f300000000000000004407000
noncomputable def e42d_target1 : Nat := 0x300000000000003201000
noncomputable def e42d_target2 : Nat := 0x300201000
noncomputable def e42d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 212
  maxLength := 7
  maxWidth := 68
  terms := 1
  left := e42d_left
  right := e42d_right
  scale := e42d_scale
  target0 := e42d_target0
  target1 := e42d_target1
  target2 := e42d_target2

theorem e42d_ok : e42d.check=true := by decide +kernel
noncomputable def e43n_left_0 : Nat := 0x20000d74ad3f19a1fc3800350ca428e081a001feeec3992fb49400007c9a3465d9560000001cf19a3bd12000000004950e676000000000004ad8140000000000005dba00000000000000203000000000000000004a09000
noncomputable def e43n_left : Nat → Nat
  | 0 => e43n_left_0
  | _ => 0
noncomputable def e43n_right_0 : Nat := 0x300201000
noncomputable def e43n_right : Nat → Nat
  | 0 => e43n_right_0
  | _ => 0
noncomputable def e43n_scale : Nat := 0x79800000000000000000005301000
noncomputable def e43n_target0 : Nat := 0x20000d74ad3f19a1fc3000800350ca428e081a000001feeec3992fb49400000007c9a3465d9560000000001cf19a3bd12000000000004950e676000000000000004ad8140000000000000005dba00000000000000000203000000000000000000005609000
noncomputable def e43n_target1 : Nat := 0x79800000000000000004701000
noncomputable def e43n_target2 : Nat := 0x300201000
noncomputable def e43n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 267
  maxLength := 9
  maxWidth := 86
  terms := 1
  left := e43n_left
  right := e43n_right
  scale := e43n_scale
  target0 := e43n_target0
  target1 := e43n_target1
  target2 := e43n_target2

theorem e43n_ok : e43n.check=true := by decide +kernel
noncomputable def e43d_left_0 : Nat := 0x7ff3943c72685b806c506d541600891ac7608d00008ecf3ed4000000488f050000000044b60000000000f300000000000003807000
noncomputable def e43d_left : Nat → Nat
  | 0 => e43d_left_0
  | _ => 0
noncomputable def e43d_right_0 : Nat := 0x300201000
noncomputable def e43d_right : Nat → Nat
  | 0 => e43d_right_0
  | _ => 0
noncomputable def e43d_scale : Nat := 0x180000000000000003d01000
noncomputable def e43d_target0 : Nat := 0xffe72878e4d0b600201b141b550580000448d63b04680000008ecf3ed4000000000911e0a0000000000112d80000000000007980000000000000004307000
noncomputable def e43d_target1 : Nat := 0x300000000000003201000
noncomputable def e43d_target2 : Nat := 0x300201000
noncomputable def e43d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 209
  maxLength := 7
  maxWidth := 67
  terms := 1
  left := e43d_left
  right := e43d_right
  scale := e43d_scale
  target0 := e43d_target0
  target1 := e43d_target1
  target2 := e43d_target2

theorem e43d_ok : e43d.check=true := by decide +kernel
noncomputable def e44n_left_0 : Nat := 0x4000244ec0ed78cbeeb80040437e93ba749000ff51cf26459b6500001ee754d6b1c9c00000038299df4c22000000003ed5550f00000000000128b1500000000000021f440000000000000048b000000000000000004b09000
noncomputable def e44n_left : Nat → Nat
  | 0 => e44n_left_0
  | _ => 0
noncomputable def e44n_right_0 : Nat := 0x300201000
noncomputable def e44n_right : Nat → Nat
  | 0 => e44n_right_0
  | _ => 0
noncomputable def e44n_scale : Nat := 0x79800000000000000000005301000
noncomputable def e44n_target0 : Nat := 0x200012276076bc65f7580080040437e93ba749000001fea39e4c8b36ca00000007b9d535ac7270000000001c14cefa611000000000003ed5550f0000000000000025162a00000000000000087d100000000000000000245800000000000000000005609000
noncomputable def e44n_target1 : Nat := 0xf3000000000000000004801000
noncomputable def e44n_target2 : Nat := 0x300201000
noncomputable def e44n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 267
  maxLength := 9
  maxWidth := 86
  terms := 1
  left := e44n_left
  right := e44n_right
  scale := e44n_scale
  target0 := e44n_target0
  target1 := e44n_target1
  target2 := e44n_target2

theorem e44n_ok : e44n.check=true := by decide +kernel
noncomputable def e44d_left_0 : Nat := 0x7ff3943c72685b806c506d541600891ac7608d00008ecf3ed4000000488f050000000044b60000000000f300000000000003807000
noncomputable def e44d_left : Nat → Nat
  | 0 => e44d_left_0
  | _ => 0
noncomputable def e44d_right_0 : Nat := 0x300201000
noncomputable def e44d_right : Nat → Nat
  | 0 => e44d_right_0
  | _ => 0
noncomputable def e44d_scale : Nat := 0x180000000000000003d01000
noncomputable def e44d_target0 : Nat := 0xffe72878e4d0b600201b141b550580000448d63b04680000008ecf3ed4000000000911e0a0000000000112d80000000000007980000000000000004307000
noncomputable def e44d_target1 : Nat := 0x300000000000003201000
noncomputable def e44d_target2 : Nat := 0x300201000
noncomputable def e44d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 209
  maxLength := 7
  maxWidth := 67
  terms := 1
  left := e44d_left
  right := e44d_right
  scale := e44d_scale
  target0 := e44d_target0
  target1 := e44d_target1
  target2 := e44d_target2

theorem e44d_ok : e44d.check=true := by decide +kernel
noncomputable def e45n_left_0 : Nat := 0x7ffffc34173b4a022346a380002e44a3c11c782e790080021de8f9bca3180c00008002649ba9216df40000007f7e76398afe9a000000007ab9d5f7aabe00000000006e9ad8ea5c0000000000004444e0040000000000000013b15b00000000000000005fd10000000000000000000580a000
noncomputable def e45n_left : Nat → Nat
  | 0 => e45n_left_0
  | _ => 0
noncomputable def e45n_right_0 : Nat := 0x300201000
noncomputable def e45n_right : Nat → Nat
  | 0 => e45n_right_0
  | _ => 0
noncomputable def e45n_scale : Nat := 0xf300000000000000000000005c01000
noncomputable def e45n_target0 : Nat := 0x1fffff0d05ced28088d1a8c0100005c89478238f05cf2000080021de8f9bca3180c0000004001324dd490b6fa000000001fdf9d8e62bfa680000000000f573abef557c0000000000006e9ad8ea5c0000000000000022227002000000000000000004ec56c000000000000000000bfa2000000000000000000000610a000
noncomputable def e45n_target1 : Nat := 0x79800000000000000000005301000
noncomputable def e45n_target2 : Nat := 0x300201000
noncomputable def e45n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 300
  maxLength := 10
  maxWidth := 97
  terms := 1
  left := e45n_left
  right := e45n_right
  scale := e45n_scale
  target0 := e45n_target0
  target1 := e45n_target1
  target2 := e45n_target2

theorem e45n_ok : e45n.check=true := by decide +kernel
noncomputable def e45d_left_0 : Nat := 0x7ff3943c72685b806c506d541600891ac7608d00008ecf3ed4000000488f050000000044b60000000000f300000000000003807000
noncomputable def e45d_left : Nat → Nat
  | 0 => e45d_left_0
  | _ => 0
noncomputable def e45d_right_0 : Nat := 0x300201000
noncomputable def e45d_right : Nat → Nat
  | 0 => e45d_right_0
  | _ => 0
noncomputable def e45d_scale : Nat := 0x300000000000000003e01000
noncomputable def e45d_target0 : Nat := 0x7ff3943c72685b000806c506d541600000891ac7608d00000008ecf3ed4000000000488f050000000000044b60000000000000f300000000000000004407000
noncomputable def e45d_target1 : Nat := 0x300000000000003201000
noncomputable def e45d_target2 : Nat := 0x300201000
noncomputable def e45d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 212
  maxLength := 7
  maxWidth := 68
  terms := 1
  left := e45d_left
  right := e45d_right
  scale := e45d_scale
  target0 := e45d_target0
  target1 := e45d_target1
  target2 := e45d_target2

theorem e45d_ok : e45d.check=true := by decide +kernel
noncomputable def e46n_left_0 : Nat := 0x2000018abd15a2eb68543dbfffbf3dab8147b8d8c10080000d27252beb02d800010041d2447d392650000001fcb5755df4df5000000003cf2b1e9d9ae00000000007076a63c780000000000006f948090000000000000002fe79800000000000000042d90000000000000000000570a000
noncomputable def e46n_left : Nat → Nat
  | 0 => e46n_left_0
  | _ => 0
noncomputable def e46n_right_0 : Nat := 0x300201000
noncomputable def e46n_right : Nat → Nat
  | 0 => e46n_right_0
  | _ => 0
noncomputable def e46n_scale : Nat := 0xf300000000000000000000005c01000
noncomputable def e46n_target0 : Nat := 0x2000018abd15a2eb68543d800fffefcf6ae051ee36304000080000d27252beb02d8000000401074911f4e4994000000001fcb5755df4df500000000000f3cac7a766b80000000000007076a63c78000000000000001be52024000000000000000002fe7980000000000000000010b64000000000000000000000610a000
noncomputable def e46n_target1 : Nat := 0x3cc00000000000000000005201000
noncomputable def e46n_target2 : Nat := 0x300201000
noncomputable def e46n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 300
  maxLength := 10
  maxWidth := 97
  terms := 1
  left := e46n_left
  right := e46n_right
  scale := e46n_scale
  target0 := e46n_target0
  target1 := e46n_target1
  target2 := e46n_target2

theorem e46n_ok : e46n.check=true := by decide +kernel
noncomputable def e46d_left_0 : Nat := 0x7ff3943c72685b806c506d541600891ac7608d00008ecf3ed4000000488f050000000044b60000000000f300000000000003807000
noncomputable def e46d_left : Nat → Nat
  | 0 => e46d_left_0
  | _ => 0
noncomputable def e46d_right_0 : Nat := 0x300201000
noncomputable def e46d_right : Nat → Nat
  | 0 => e46d_right_0
  | _ => 0
noncomputable def e46d_scale : Nat := 0x300000000000000003e01000
noncomputable def e46d_target0 : Nat := 0x7ff3943c72685b000806c506d541600000891ac7608d00000008ecf3ed4000000000488f050000000000044b60000000000000f300000000000000004407000
noncomputable def e46d_target1 : Nat := 0x300000000000003201000
noncomputable def e46d_target2 : Nat := 0x300201000
noncomputable def e46d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 212
  maxLength := 7
  maxWidth := 68
  terms := 1
  left := e46d_left
  right := e46d_right
  scale := e46d_scale
  target0 := e46d_target0
  target1 := e46d_target1
  target2 := e46d_target2

theorem e46d_ok : e46d.check=true := by decide +kernel
noncomputable def e47n_left_0 : Nat := 0x7fffb2bfb91cbd7b63397ffde5ab8db483517b008060506590dfb864000083e6afb920501c0000008cd5efc8e42e00000000b57ee64e1a0000000000e8ce44540000000000009fc54c0000000000000086e10000000000000000830000000000000000000500a000
noncomputable def e47n_left : Nat → Nat
  | 0 => e47n_left_0
  | _ => 0
noncomputable def e47n_right_0 : Nat := 0x300201000
noncomputable def e47n_right : Nat → Nat
  | 0 => e47n_right_0
  | _ => 0
noncomputable def e47n_scale : Nat := 0x7980000000000000000000005b01000
noncomputable def e47n_target0 : Nat := 0x7fffb2bfb91cbd7b63390001fff796ae36d20d45ec000008060506590dfb864000000020f9abee48140700000000008cd5efc8e42e000000000002d5fb9938680000000000000e8ce445400000000000000027f15300000000000000000086e1000000000000000000020c00000000000000000000005e0a000
noncomputable def e47n_target1 : Nat := 0x1e60000000000000000004d01000
noncomputable def e47n_target2 : Nat := 0x300201000
noncomputable def e47n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 291
  maxLength := 10
  maxWidth := 94
  terms := 1
  left := e47n_left
  right := e47n_right
  scale := e47n_scale
  target0 := e47n_target0
  target1 := e47n_target1
  target2 := e47n_target2

theorem e47n_ok : e47n.check=true := by decide +kernel
noncomputable def e47d_left_0 : Nat := 0x7ff3943c72685b806c506d541600891ac7608d00008ecf3ed4000000488f050000000044b60000000000f300000000000003807000
noncomputable def e47d_left : Nat → Nat
  | 0 => e47d_left_0
  | _ => 0
noncomputable def e47d_right_0 : Nat := 0x300201000
noncomputable def e47d_right : Nat → Nat
  | 0 => e47d_right_0
  | _ => 0
noncomputable def e47d_scale : Nat := 0x180000000000000003d01000
noncomputable def e47d_target0 : Nat := 0xffe72878e4d0b600201b141b550580000448d63b04680000008ecf3ed4000000000911e0a0000000000112d80000000000007980000000000000004307000
noncomputable def e47d_target1 : Nat := 0x300000000000003201000
noncomputable def e47d_target2 : Nat := 0x300201000
noncomputable def e47d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 209
  maxLength := 7
  maxWidth := 67
  terms := 1
  left := e47d_left
  right := e47d_right
  scale := e47d_scale
  target0 := e47d_target0
  target1 := e47d_target1
  target2 := e47d_target2

theorem e47d_ok : e47d.check=true := by decide +kernel
noncomputable def e48n_left_0 : Nat := 0x20000101b0a9983887ec66fff905d17c784d054a900801f6309257baf52600004126c39e73b5d6d0000002142087c7d5af4000000013013988b35e0000000000ce72751ce0000000000004d306b100000000000000146ed60000000000000000e810000000000000000000550a000
noncomputable def e48n_left : Nat → Nat
  | 0 => e48n_left_0
  | _ => 0
noncomputable def e48n_right_0 : Nat := 0x300201000
noncomputable def e48n_right : Nat → Nat
  | 0 => e48n_right_0
  | _ => 0
noncomputable def e48n_scale : Nat := 0x7980000000000000000000005b01000
noncomputable def e48n_target0 : Nat := 0x20000101b0a9983887ec66003ffe41745f1e134152a40000801f6309257baf5260000001049b0e79ced75b4000000002142087c7d5af400000000004c04e622cd78000000000000ce72751ce00000000000000134c1ac40000000000000000146ed60000000000000000003a040000000000000000000005f0a000
noncomputable def e48n_target1 : Nat := 0x1e600000000000000000005101000
noncomputable def e48n_target2 : Nat := 0x300201000
noncomputable def e48n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 294
  maxLength := 10
  maxWidth := 95
  terms := 1
  left := e48n_left
  right := e48n_right
  scale := e48n_scale
  target0 := e48n_target0
  target1 := e48n_target1
  target2 := e48n_target2

theorem e48n_ok : e48n.check=true := by decide +kernel
noncomputable def e48d_left_0 : Nat := 0x7ff3943c72685b806c506d541600891ac7608d00008ecf3ed4000000488f050000000044b60000000000f300000000000003807000
noncomputable def e48d_left : Nat → Nat
  | 0 => e48d_left_0
  | _ => 0
noncomputable def e48d_right_0 : Nat := 0x300201000
noncomputable def e48d_right : Nat → Nat
  | 0 => e48d_right_0
  | _ => 0
noncomputable def e48d_scale : Nat := 0x180000000000000003d01000
noncomputable def e48d_target0 : Nat := 0xffe72878e4d0b600201b141b550580000448d63b04680000008ecf3ed4000000000911e0a0000000000112d80000000000007980000000000000004307000
noncomputable def e48d_target1 : Nat := 0x300000000000003201000
noncomputable def e48d_target2 : Nat := 0x300201000
noncomputable def e48d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 209
  maxLength := 7
  maxWidth := 67
  terms := 1
  left := e48d_left
  right := e48d_right
  scale := e48d_scale
  target0 := e48d_target0
  target1 := e48d_target1
  target2 := e48d_target2

theorem e48d_ok : e48d.check=true := by decide +kernel
noncomputable def e49n_left_0 : Nat := 0x7c1d69261285900148c0001b00000001e04000
noncomputable def e49n_left : Nat → Nat
  | 0 => e49n_left_0
  | _ => 0
noncomputable def e49n_right_0 : Nat := 0x300201000
noncomputable def e49n_right : Nat → Nat
  | 0 => e49n_right_0
  | _ => 0
noncomputable def e49n_scale : Nat := 0x30000000002201000
noncomputable def e49n_target0 : Nat := 0x7c1d692402128590000148c000001b0000000002604000
noncomputable def e49n_target1 : Nat := 0x300000001a01000
noncomputable def e49n_target2 : Nat := 0x300201000
noncomputable def e49n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 120
  maxLength := 4
  maxWidth := 38
  terms := 1
  left := e49n_left
  right := e49n_right
  scale := e49n_scale
  target0 := e49n_target0
  target1 := e49n_target1
  target2 := e49n_target2

theorem e49n_ok : e49n.check=true := by decide +kernel
noncomputable def e49d_left_0 : Nat := 0x300201000
noncomputable def e49d_left : Nat → Nat
  | 0 => e49d_left_0
  | _ => 0
noncomputable def e49d_right_0 : Nat := 0x300201000
noncomputable def e49d_right : Nat → Nat
  | 0 => e49d_right_0
  | _ => 0
noncomputable def e49d_scale : Nat := 0x30000a01000
noncomputable def e49d_target0 : Nat := 0x30000a01000
noncomputable def e49d_target1 : Nat := 0x300201000
noncomputable def e49d_target2 : Nat := 0x300201000
noncomputable def e49d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 30
  maxLength := 1
  maxWidth := 10
  terms := 1
  left := e49d_left
  right := e49d_right
  scale := e49d_scale
  target0 := e49d_target0
  target1 := e49d_target1
  target2 := e49d_target2

theorem e49d_ok : e49d.check=true := by decide +kernel
end ThomsonNegative.Certificate.Bridges.RFChecks
