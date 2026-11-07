import ThomsonNegative.Structure.Packed.IdentityKernel
namespace ThomsonNegative.Certificate.Bridges.RFChecks
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
noncomputable def e60n_left_0 : Nat := 0x3f27f5dbc005000001503000
noncomputable def e60n_left : Nat → Nat
  | 0 => e60n_left_0
  | _ => 0
noncomputable def e60n_right_0 : Nat := 0x300201000
noncomputable def e60n_right : Nat → Nat
  | 0 => e60n_right_0
  | _ => 0
noncomputable def e60n_scale : Nat := 0x300000001a01000
noncomputable def e60n_target0 : Nat := 0x3f27f401dbc0000500000001d03000
noncomputable def e60n_target1 : Nat := 0x3000001201000
noncomputable def e60n_target2 : Nat := 0x300201000
noncomputable def e60n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 91
  maxLength := 3
  maxWidth := 29
  terms := 1
  left := e60n_left
  right := e60n_right
  scale := e60n_scale
  target0 := e60n_target0
  target1 := e60n_target1
  target2 := e60n_target2

theorem e60n_ok : e60n.check=true := by decide +kernel
noncomputable def e60d_left_0 : Nat := 0x300201000
noncomputable def e60d_left : Nat → Nat
  | 0 => e60d_left_0
  | _ => 0
noncomputable def e60d_right_0 : Nat := 0x300201000
noncomputable def e60d_right : Nat → Nat
  | 0 => e60d_right_0
  | _ => 0
noncomputable def e60d_scale : Nat := 0x30000a01000
noncomputable def e60d_target0 : Nat := 0x30000a01000
noncomputable def e60d_target1 : Nat := 0x300201000
noncomputable def e60d_target2 : Nat := 0x300201000
noncomputable def e60d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 30
  maxLength := 1
  maxWidth := 10
  terms := 1
  left := e60d_left
  right := e60d_right
  scale := e60d_scale
  target0 := e60d_target0
  target1 := e60d_target1
  target2 := e60d_target2

theorem e60d_ok : e60d.check=true := by decide +kernel
noncomputable def e61n_left_0 : Nat := 0x3ffc7c056fb803df7dc8010cd86480002b0a200000064b0000000002b05000
noncomputable def e61n_left : Nat → Nat
  | 0 => e61n_left_0
  | _ => 0
noncomputable def e61n_right_0 : Nat := 0x300201000
noncomputable def e61n_right : Nat → Nat
  | 0 => e61n_right_0
  | _ => 0
noncomputable def e61n_scale : Nat := 0x798000000000003301000
noncomputable def e61n_target0 : Nat := 0x3ffc7c056fb00803df7dc800010cd8648000002b0a20000000064b000000000003305000
noncomputable def e61n_target1 : Nat := 0x7980000000002b01000
noncomputable def e61n_target2 : Nat := 0x300201000
noncomputable def e61n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 159
  maxLength := 5
  maxWidth := 51
  terms := 1
  left := e61n_left
  right := e61n_right
  scale := e61n_scale
  target0 := e61n_target0
  target1 := e61n_target1
  target2 := e61n_target2

theorem e61n_ok : e61n.check=true := by decide +kernel
noncomputable def e61d_left_0 : Nat := 0x7ff3943c72685b806c506d541600891ac7608d00008ecf3ed4000000488f050000000044b60000000000f300000000000003807000
noncomputable def e61d_left : Nat → Nat
  | 0 => e61d_left_0
  | _ => 0
noncomputable def e61d_right_0 : Nat := 0x300201000
noncomputable def e61d_right : Nat → Nat
  | 0 => e61d_right_0
  | _ => 0
noncomputable def e61d_scale : Nat := 0x180000000000000003d01000
noncomputable def e61d_target0 : Nat := 0xffe72878e4d0b600201b141b550580000448d63b04680000008ecf3ed4000000000911e0a0000000000112d80000000000007980000000000000004307000
noncomputable def e61d_target1 : Nat := 0x300000000000003201000
noncomputable def e61d_target2 : Nat := 0x300201000
noncomputable def e61d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 209
  maxLength := 7
  maxWidth := 67
  terms := 1
  left := e61d_left
  right := e61d_right
  scale := e61d_scale
  target0 := e61d_target0
  target1 := e61d_target1
  target2 := e61d_target2

theorem e61d_ok : e61d.check=true := by decide +kernel
noncomputable def e62n_left_0 : Nat := 0x8001bff34c6e600b7f4c1cf007d6a3d4a800017249ee000000327340000000193000000000003206000
noncomputable def e62n_left : Nat → Nat
  | 0 => e62n_left_0
  | _ => 0
noncomputable def e62n_right_0 : Nat := 0x300201000
noncomputable def e62n_right : Nat → Nat
  | 0 => e62n_right_0
  | _ => 0
noncomputable def e62n_scale : Nat := 0x79800000000000003b01000
noncomputable def e62n_target0 : Nat := 0x20006ffcd31b9004016fe9839e00007d6a3d4a8000000b924f7000000000c9cd000000000032600000000000003b06000
noncomputable def e62n_target1 : Nat := 0x3cc000000000003201000
noncomputable def e62n_target2 : Nat := 0x300201000
noncomputable def e62n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 184
  maxLength := 6
  maxWidth := 59
  terms := 1
  left := e62n_left
  right := e62n_right
  scale := e62n_scale
  target0 := e62n_target0
  target1 := e62n_target1
  target2 := e62n_target2

theorem e62n_ok : e62n.check=true := by decide +kernel
noncomputable def e62d_left_0 : Nat := 0x7ff3943c72685b806c506d541600891ac7608d00008ecf3ed4000000488f050000000044b60000000000f300000000000003807000
noncomputable def e62d_left : Nat → Nat
  | 0 => e62d_left_0
  | _ => 0
noncomputable def e62d_right_0 : Nat := 0x300201000
noncomputable def e62d_right : Nat → Nat
  | 0 => e62d_right_0
  | _ => 0
noncomputable def e62d_scale : Nat := 0x180000000000000003d01000
noncomputable def e62d_target0 : Nat := 0xffe72878e4d0b600201b141b550580000448d63b04680000008ecf3ed4000000000911e0a0000000000112d80000000000007980000000000000004307000
noncomputable def e62d_target1 : Nat := 0x300000000000003201000
noncomputable def e62d_target2 : Nat := 0x300201000
noncomputable def e62d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 209
  maxLength := 7
  maxWidth := 67
  terms := 1
  left := e62d_left
  right := e62d_right
  scale := e62d_scale
  target0 := e62d_target0
  target1 := e62d_target1
  target2 := e62d_target2

theorem e62d_ok : e62d.check=true := by decide +kernel
noncomputable def e63n_left_0 : Nat := 0x200196fa08ecc004ce36bf007a84d6540000a3fc38000000c968000000043000000000002f06000
noncomputable def e63n_left : Nat → Nat
  | 0 => e63n_left_0
  | _ => 0
noncomputable def e63n_right_0 : Nat := 0x300201000
noncomputable def e63n_right : Nat → Nat
  | 0 => e63n_right_0
  | _ => 0
noncomputable def e63n_scale : Nat := 0x79800000000000003b01000
noncomputable def e63n_target0 : Nat := 0x200196fa08ec8004004ce36bf000007a84d6540000000a3fc38000000000c968000000000043000000000000003b06000
noncomputable def e63n_target1 : Nat := 0x79800000000002f01000
noncomputable def e63n_target2 : Nat := 0x300201000
noncomputable def e63n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 184
  maxLength := 6
  maxWidth := 59
  terms := 1
  left := e63n_left
  right := e63n_right
  scale := e63n_scale
  target0 := e63n_target0
  target1 := e63n_target1
  target2 := e63n_target2

theorem e63n_ok : e63n.check=true := by decide +kernel
noncomputable def e63d_left_0 : Nat := 0x7ff3943c72685b806c506d541600891ac7608d00008ecf3ed4000000488f050000000044b60000000000f300000000000003807000
noncomputable def e63d_left : Nat → Nat
  | 0 => e63d_left_0
  | _ => 0
noncomputable def e63d_right_0 : Nat := 0x300201000
noncomputable def e63d_right : Nat → Nat
  | 0 => e63d_right_0
  | _ => 0
noncomputable def e63d_scale : Nat := 0x180000000000000003d01000
noncomputable def e63d_target0 : Nat := 0xffe72878e4d0b600201b141b550580000448d63b04680000008ecf3ed4000000000911e0a0000000000112d80000000000007980000000000000004307000
noncomputable def e63d_target1 : Nat := 0x300000000000003201000
noncomputable def e63d_target2 : Nat := 0x300201000
noncomputable def e63d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 209
  maxLength := 7
  maxWidth := 67
  terms := 1
  left := e63d_left
  right := e63d_right
  scale := e63d_scale
  target0 := e63d_target0
  target1 := e63d_target1
  target2 := e63d_target2

theorem e63d_ok : e63d.check=true := by decide +kernel
noncomputable def e64n_left_0 : Nat := 0x200033e83176d1157ff4ca136f572801fec3c8c058300008036b3e5b0000001ee5738b000000004d2ca80000000000b7d00000000000003e07000
noncomputable def e64n_left : Nat → Nat
  | 0 => e64n_left_0
  | _ => 0
noncomputable def e64n_right_0 : Nat := 0x300201000
noncomputable def e64n_right : Nat → Nat
  | 0 => e64n_right_0
  | _ => 0
noncomputable def e64n_scale : Nat := 0xf300000000000000004401000
noncomputable def e64n_target0 : Nat := 0x200033e83176d115007ff4ca136f57280001fec3c8c05830000008036b3e5b000000001ee5738b00000000004d2ca8000000000000b7d0000000000000004607000
noncomputable def e64n_target1 : Nat := 0xf3000000000000003c01000
noncomputable def e64n_target2 : Nat := 0x300201000
noncomputable def e64n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 218
  maxLength := 7
  maxWidth := 70
  terms := 1
  left := e64n_left
  right := e64n_right
  scale := e64n_scale
  target0 := e64n_target0
  target1 := e64n_target1
  target2 := e64n_target2

theorem e64n_ok : e64n.check=true := by decide +kernel
noncomputable def e64d_left_0 : Nat := 0x7ff3943c72685b806c506d541600891ac7608d00008ecf3ed4000000488f050000000044b60000000000f300000000000003807000
noncomputable def e64d_left : Nat → Nat
  | 0 => e64d_left_0
  | _ => 0
noncomputable def e64d_right_0 : Nat := 0x300201000
noncomputable def e64d_right : Nat → Nat
  | 0 => e64d_right_0
  | _ => 0
noncomputable def e64d_scale : Nat := 0x300000000000000003e01000
noncomputable def e64d_target0 : Nat := 0x7ff3943c72685b000806c506d541600000891ac7608d00000008ecf3ed4000000000488f050000000000044b60000000000000f300000000000000004407000
noncomputable def e64d_target1 : Nat := 0x300000000000003201000
noncomputable def e64d_target2 : Nat := 0x300201000
noncomputable def e64d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 212
  maxLength := 7
  maxWidth := 68
  terms := 1
  left := e64d_left
  right := e64d_right
  scale := e64d_scale
  target0 := e64d_target0
  target1 := e64d_target1
  target2 := e64d_target2

theorem e64d_ok : e64d.check=true := by decide +kernel
noncomputable def e65n_left_0 : Nat := 0xfffc1088fb212dffa22f5a32b004195be63bd0000a3c511a800000194a1540000000263b00000000004300000000000003707000
noncomputable def e65n_left : Nat → Nat
  | 0 => e65n_left_0
  | _ => 0
noncomputable def e65n_right_0 : Nat := 0x300201000
noncomputable def e65n_right : Nat → Nat
  | 0 => e65n_right_0
  | _ => 0
noncomputable def e65n_scale : Nat := 0x7980000000000000004301000
noncomputable def e65n_target0 : Nat := 0xfffc1088fb212c001ffa22f5a32b000004195be63bd0000000a3c511a800000000194a1540000000000263b00000000000004300000000000000004307000
noncomputable def e65n_target1 : Nat := 0x7980000000000003701000
noncomputable def e65n_target2 : Nat := 0x300201000
noncomputable def e65n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 209
  maxLength := 7
  maxWidth := 67
  terms := 1
  left := e65n_left
  right := e65n_right
  scale := e65n_scale
  target0 := e65n_target0
  target1 := e65n_target1
  target2 := e65n_target2

theorem e65n_ok : e65n.check=true := by decide +kernel
noncomputable def e65d_left_0 : Nat := 0x7ff3943c72685b806c506d541600891ac7608d00008ecf3ed4000000488f050000000044b60000000000f300000000000003807000
noncomputable def e65d_left : Nat → Nat
  | 0 => e65d_left_0
  | _ => 0
noncomputable def e65d_right_0 : Nat := 0x300201000
noncomputable def e65d_right : Nat → Nat
  | 0 => e65d_right_0
  | _ => 0
noncomputable def e65d_scale : Nat := 0x180000000000000003d01000
noncomputable def e65d_target0 : Nat := 0xffe72878e4d0b600201b141b550580000448d63b04680000008ecf3ed4000000000911e0a0000000000112d80000000000007980000000000000004307000
noncomputable def e65d_target1 : Nat := 0x300000000000003201000
noncomputable def e65d_target2 : Nat := 0x300201000
noncomputable def e65d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 209
  maxLength := 7
  maxWidth := 67
  terms := 1
  left := e65d_left
  right := e65d_right
  scale := e65d_scale
  target0 := e65d_target0
  target1 := e65d_target1
  target2 := e65d_target2

theorem e65d_ok : e65d.check=true := by decide +kernel
noncomputable def e66n_left_0 : Nat := 0x3fffd372e401955ff4b2cb76e940104a74b5f430000a9d1dd36000000705a12c0000000221540000000000bd00000000000003907000
noncomputable def e66n_left : Nat → Nat
  | 0 => e66n_left_0
  | _ => 0
noncomputable def e66n_right_0 : Nat := 0x300201000
noncomputable def e66n_right : Nat → Nat
  | 0 => e66n_right_0
  | _ => 0
noncomputable def e66n_scale : Nat := 0x7980000000000000004301000
noncomputable def e66n_target0 : Nat := 0xffff4dcb900655001ff4b2cb76e9400004129d2d7d0c000000a9d1dd36000000001c1684b0000000000221540000000000002f40000000000000004307000
noncomputable def e66n_target1 : Nat := 0x1e600000000000003901000
noncomputable def e66n_target2 : Nat := 0x300201000
noncomputable def e66n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 209
  maxLength := 7
  maxWidth := 67
  terms := 1
  left := e66n_left
  right := e66n_right
  scale := e66n_scale
  target0 := e66n_target0
  target1 := e66n_target1
  target2 := e66n_target2

theorem e66n_ok : e66n.check=true := by decide +kernel
noncomputable def e66d_left_0 : Nat := 0x7ff3943c72685b806c506d541600891ac7608d00008ecf3ed4000000488f050000000044b60000000000f300000000000003807000
noncomputable def e66d_left : Nat → Nat
  | 0 => e66d_left_0
  | _ => 0
noncomputable def e66d_right_0 : Nat := 0x300201000
noncomputable def e66d_right : Nat → Nat
  | 0 => e66d_right_0
  | _ => 0
noncomputable def e66d_scale : Nat := 0x180000000000000003d01000
noncomputable def e66d_target0 : Nat := 0xffe72878e4d0b600201b141b550580000448d63b04680000008ecf3ed4000000000911e0a0000000000112d80000000000007980000000000000004307000
noncomputable def e66d_target1 : Nat := 0x300000000000003201000
noncomputable def e66d_target2 : Nat := 0x300201000
noncomputable def e66d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 209
  maxLength := 7
  maxWidth := 67
  terms := 1
  left := e66d_left
  right := e66d_right
  scale := e66d_scale
  target0 := e66d_target0
  target1 := e66d_target1
  target2 := e66d_target2

theorem e66d_ok : e66d.check=true := by decide +kernel
noncomputable def e67n_left_0 : Nat := 0x800024363e1946cfcbffebb7b59045a5401ffbe9653bd5ca0001009b53b5d01000000859bd9cad80000000548dc33c00000000033b50e0000000000012db0000000000000004508000
noncomputable def e67n_left : Nat → Nat
  | 0 => e67n_left_0
  | _ => 0
noncomputable def e67n_right_0 : Nat := 0x300201000
noncomputable def e67n_right : Nat → Nat
  | 0 => e67n_right_0
  | _ => 0
noncomputable def e67n_scale : Nat := 0xf30000000000000000004c01000
noncomputable def e67n_target0 : Nat := 0x800024363e1946cfc801fff5dbdac822d2a00007fefa594ef57280000020136a76ba0200000000859bd9cad80000000002a46e19e000000000000ced438000000000000025b6000000000000000004e08000
noncomputable def e67n_target1 : Nat := 0x7980000000000000004301000
noncomputable def e67n_target2 : Nat := 0x300201000
noncomputable def e67n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 243
  maxLength := 8
  maxWidth := 78
  terms := 1
  left := e67n_left
  right := e67n_right
  scale := e67n_scale
  target0 := e67n_target0
  target1 := e67n_target1
  target2 := e67n_target2

theorem e67n_ok : e67n.check=true := by decide +kernel
noncomputable def e67d_left_0 : Nat := 0x7ff3943c72685b806c506d541600891ac7608d00008ecf3ed4000000488f050000000044b60000000000f300000000000003807000
noncomputable def e67d_left : Nat → Nat
  | 0 => e67d_left_0
  | _ => 0
noncomputable def e67d_right_0 : Nat := 0x300201000
noncomputable def e67d_right : Nat → Nat
  | 0 => e67d_right_0
  | _ => 0
noncomputable def e67d_scale : Nat := 0x300000000000000003e01000
noncomputable def e67d_target0 : Nat := 0x7ff3943c72685b000806c506d541600000891ac7608d00000008ecf3ed4000000000488f050000000000044b60000000000000f300000000000000004407000
noncomputable def e67d_target1 : Nat := 0x300000000000003201000
noncomputable def e67d_target2 : Nat := 0x300201000
noncomputable def e67d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 212
  maxLength := 7
  maxWidth := 68
  terms := 1
  left := e67d_left
  right := e67d_right
  scale := e67d_scale
  target0 := e67d_target0
  target1 := e67d_target1
  target2 := e67d_target2

theorem e67d_ok : e67d.check=true := by decide +kernel
noncomputable def e68n_left_0 : Nat := 0x7fffb722cc6c0b2bb800570442a5a08f00800e74e0cb1bf00007ea2e1e791300000083f6ca08100000000b9fc8dd0000000000d59450000000000007410000000000000004408000
noncomputable def e68n_left : Nat → Nat
  | 0 => e68n_left_0
  | _ => 0
noncomputable def e68n_right_0 : Nat := 0x300201000
noncomputable def e68n_right : Nat → Nat
  | 0 => e68n_right_0
  | _ => 0
noncomputable def e68n_scale : Nat := 0xf30000000000000000004c01000
noncomputable def e68n_target0 : Nat := 0x7fffb722cc6c0b2bb0020015c110a96823c0000800e74e0cb1bf0000001fa8b879e44c0000000083f6ca08100000000002e7f2374000000000000d5945000000000000001d04000000000000000004e08000
noncomputable def e68n_target1 : Nat := 0x3cc0000000000000004201000
noncomputable def e68n_target2 : Nat := 0x300201000
noncomputable def e68n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 243
  maxLength := 8
  maxWidth := 78
  terms := 1
  left := e68n_left
  right := e68n_right
  scale := e68n_scale
  target0 := e68n_target0
  target1 := e68n_target1
  target2 := e68n_target2

theorem e68n_ok : e68n.check=true := by decide +kernel
noncomputable def e68d_left_0 : Nat := 0x7ff3943c72685b806c506d541600891ac7608d00008ecf3ed4000000488f050000000044b60000000000f300000000000003807000
noncomputable def e68d_left : Nat → Nat
  | 0 => e68d_left_0
  | _ => 0
noncomputable def e68d_right_0 : Nat := 0x300201000
noncomputable def e68d_right : Nat → Nat
  | 0 => e68d_right_0
  | _ => 0
noncomputable def e68d_scale : Nat := 0x300000000000000003e01000
noncomputable def e68d_target0 : Nat := 0x7ff3943c72685b000806c506d541600000891ac7608d00000008ecf3ed4000000000488f050000000000044b60000000000000f300000000000000004407000
noncomputable def e68d_target1 : Nat := 0x300000000000003201000
noncomputable def e68d_target2 : Nat := 0x300201000
noncomputable def e68d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 212
  maxLength := 7
  maxWidth := 68
  terms := 1
  left := e68d_left
  right := e68d_right
  scale := e68d_scale
  target0 := e68d_target0
  target1 := e68d_target1
  target2 := e68d_target2

theorem e68d_ok : e68d.check=true := by decide +kernel
noncomputable def e69n_left_0 : Nat := 0x8003eaa445db26c7c008f6475e8cd4c01eeac6c2434060000af6fb0504700000037ace55e800000003f63da40000000001f5e2000000000000bd0000000000000004108000
noncomputable def e69n_left : Nat → Nat
  | 0 => e69n_left_0
  | _ => 0
noncomputable def e69n_right_0 : Nat := 0x300201000
noncomputable def e69n_right : Nat → Nat
  | 0 => e69n_right_0
  | _ => 0
noncomputable def e69n_scale : Nat := 0x798000000000000000004b01000
noncomputable def e69n_target0 : Nat := 0x8003eaa445db26c78010023d91d7a335300001eeac6c2434060000002bdbec1411c0000000037ace55e80000000000fd8f690000000000001f5e2000000000000002f4000000000000000004b08000
noncomputable def e69n_target1 : Nat := 0x1e60000000000000004101000
noncomputable def e69n_target2 : Nat := 0x300201000
noncomputable def e69n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 234
  maxLength := 8
  maxWidth := 75
  terms := 1
  left := e69n_left
  right := e69n_right
  scale := e69n_scale
  target0 := e69n_target0
  target1 := e69n_target1
  target2 := e69n_target2

theorem e69n_ok : e69n.check=true := by decide +kernel
noncomputable def e69d_left_0 : Nat := 0x7ff3943c72685b806c506d541600891ac7608d00008ecf3ed4000000488f050000000044b60000000000f300000000000003807000
noncomputable def e69d_left : Nat → Nat
  | 0 => e69d_left_0
  | _ => 0
noncomputable def e69d_right_0 : Nat := 0x300201000
noncomputable def e69d_right : Nat → Nat
  | 0 => e69d_right_0
  | _ => 0
noncomputable def e69d_scale : Nat := 0x180000000000000003d01000
noncomputable def e69d_target0 : Nat := 0xffe72878e4d0b600201b141b550580000448d63b04680000008ecf3ed4000000000911e0a0000000000112d80000000000007980000000000000004307000
noncomputable def e69d_target1 : Nat := 0x300000000000003201000
noncomputable def e69d_target2 : Nat := 0x300201000
noncomputable def e69d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 209
  maxLength := 7
  maxWidth := 67
  terms := 1
  left := e69d_left
  right := e69d_right
  scale := e69d_scale
  target0 := e69d_target0
  target1 := e69d_target1
  target2 := e69d_target2

theorem e69d_ok : e69d.check=true := by decide +kernel
end ThomsonNegative.Certificate.Bridges.RFChecks
