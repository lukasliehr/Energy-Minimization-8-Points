import ThomsonNegative.Structure.Packed.IdentityKernel
namespace ThomsonNegative.Certificate.Bridges.RFChecks
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
noncomputable def e70n_left_0 : Nat := 0x80001e77268288dec02303f9f21132401f778f45ea7b200009e8b9a6865000000129ec133800000005167eac00000000031786000000000000670000000000000004108000
noncomputable def e70n_left : Nat → Nat
  | 0 => e70n_left_0
  | _ => 0
noncomputable def e70n_right_0 : Nat := 0x300201000
noncomputable def e70n_right : Nat → Nat
  | 0 => e70n_right_0
  | _ => 0
noncomputable def e70n_scale : Nat := 0x798000000000000000004b01000
noncomputable def e70n_target0 : Nat := 0x80001e77268288de801008c0fe7c844c900001f778f45ea7b200000027a2e69a19400000000129ec13380000000001459fab000000000000317860000000000000019c000000000000000004b08000
noncomputable def e70n_target1 : Nat := 0x1e60000000000000004101000
noncomputable def e70n_target2 : Nat := 0x300201000
noncomputable def e70n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 234
  maxLength := 8
  maxWidth := 75
  terms := 1
  left := e70n_left
  right := e70n_right
  scale := e70n_scale
  target0 := e70n_target0
  target1 := e70n_target1
  target2 := e70n_target2

theorem e70n_ok : e70n.check=true := by decide +kernel
noncomputable def e70d_left_0 : Nat := 0x7ff3943c72685b806c506d541600891ac7608d00008ecf3ed4000000488f050000000044b60000000000f300000000000003807000
noncomputable def e70d_left : Nat → Nat
  | 0 => e70d_left_0
  | _ => 0
noncomputable def e70d_right_0 : Nat := 0x300201000
noncomputable def e70d_right : Nat → Nat
  | 0 => e70d_right_0
  | _ => 0
noncomputable def e70d_scale : Nat := 0x180000000000000003d01000
noncomputable def e70d_target0 : Nat := 0xffe72878e4d0b600201b141b550580000448d63b04680000008ecf3ed4000000000911e0a0000000000112d80000000000007980000000000000004307000
noncomputable def e70d_target1 : Nat := 0x300000000000003201000
noncomputable def e70d_target2 : Nat := 0x300201000
noncomputable def e70d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 209
  maxLength := 7
  maxWidth := 67
  terms := 1
  left := e70d_left
  right := e70d_right
  scale := e70d_scale
  target0 := e70d_target0
  target1 := e70d_target1
  target2 := e70d_target2

theorem e70d_ok : e70d.check=true := by decide +kernel
noncomputable def e71n_left_0 : Nat := 0xeb50000a02000
noncomputable def e71n_left : Nat → Nat
  | 0 => e71n_left_0
  | _ => 0
noncomputable def e71n_right_0 : Nat := 0x300201000
noncomputable def e71n_right : Nat → Nat
  | 0 => e71n_right_0
  | _ => 0
noncomputable def e71n_scale : Nat := 0x3000001201000
noncomputable def e71n_target0 : Nat := 0xeb401000001202000
noncomputable def e71n_target1 : Nat := 0x30000a01000
noncomputable def e71n_target2 : Nat := 0x300201000
noncomputable def e71n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 57
  maxLength := 2
  maxWidth := 18
  terms := 1
  left := e71n_left
  right := e71n_right
  scale := e71n_scale
  target0 := e71n_target0
  target1 := e71n_target1
  target2 := e71n_target2

theorem e71n_ok : e71n.check=true := by decide +kernel
noncomputable def e71d_left_0 : Nat := 0x300201000
noncomputable def e71d_left : Nat → Nat
  | 0 => e71d_left_0
  | _ => 0
noncomputable def e71d_right_0 : Nat := 0x300201000
noncomputable def e71d_right : Nat → Nat
  | 0 => e71d_right_0
  | _ => 0
noncomputable def e71d_scale : Nat := 0x30000a01000
noncomputable def e71d_target0 : Nat := 0x30000a01000
noncomputable def e71d_target1 : Nat := 0x300201000
noncomputable def e71d_target2 : Nat := 0x300201000
noncomputable def e71d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 30
  maxLength := 1
  maxWidth := 10
  terms := 1
  left := e71d_left
  right := e71d_right
  scale := e71d_scale
  target0 := e71d_target0
  target1 := e71d_target1
  target2 := e71d_target2

theorem e71d_ok : e71d.check=true := by decide +kernel
noncomputable def e72n_left_0 : Nat := 0x3ff5e03e689612dfd6f734ced6c00fda56ece5d00007054db4a0000002896e540000000000ac00000000012300000000000003907000
noncomputable def e72n_left : Nat → Nat
  | 0 => e72n_left_0
  | _ => 0
noncomputable def e72n_right_0 : Nat := 0x300201000
noncomputable def e72n_right : Nat → Nat
  | 0 => e72n_right_0
  | _ => 0
noncomputable def e72n_scale : Nat := 0x680000000000000003f01000
noncomputable def e72n_target0 : Nat := 0xffd780f9a2584b001fd6f734ced6c00003f695bb39740000007054db4a000000000a25b950000000000000ac00000000000048c0000000000000004307000
noncomputable def e72n_target1 : Nat := 0x1a00000000000003501000
noncomputable def e72n_target2 : Nat := 0x300201000
noncomputable def e72n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 209
  maxLength := 7
  maxWidth := 67
  terms := 1
  left := e72n_left
  right := e72n_right
  scale := e72n_scale
  target0 := e72n_target0
  target1 := e72n_target1
  target2 := e72n_target2

theorem e72n_ok : e72n.check=true := by decide +kernel
noncomputable def e72d_left_0 : Nat := 0xfceee18557a7676e00565d380000cf800000150000000002505000
noncomputable def e72d_left : Nat → Nat
  | 0 => e72d_left_0
  | _ => 0
noncomputable def e72d_right_0 : Nat := 0x300201000
noncomputable def e72d_right : Nat → Nat
  | 0 => e72d_right_0
  | _ => 0
noncomputable def e72d_scale : Nat := 0x18000000000002d01000
noncomputable def e72d_target0 : Nat := 0x7e7770c2a8007a7676e00000acba7000000033e000000000a8000000000003005000
noncomputable def e72d_target1 : Nat := 0x30000000002201000
noncomputable def e72d_target2 : Nat := 0x300201000
noncomputable def e72d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 150
  maxLength := 5
  maxWidth := 48
  terms := 1
  left := e72d_left
  right := e72d_right
  scale := e72d_scale
  target0 := e72d_target0
  target1 := e72d_target1
  target2 := e72d_target2

theorem e72d_ok : e72d.check=true := by decide +kernel
noncomputable def e73n_left_0 : Nat := 0x7fff35ff90b8ef9980373361bcb9f50082607aefdc850000863477e161000000a8eb9f3b00000000fe9bef00000000009d670000000000007b0000000000000004008000
noncomputable def e73n_left : Nat → Nat
  | 0 => e73n_left_0
  | _ => 0
noncomputable def e73n_right_0 : Nat := 0x300201000
noncomputable def e73n_right : Nat → Nat
  | 0 => e73n_right_0
  | _ => 0
noncomputable def e73n_scale : Nat := 0x68000000000000000004701000
noncomputable def e73n_target0 : Nat := 0x7fff35ff90b8ef99001006e66c37973ea000020981ebbf7214000000431a3bf0b0800000000a8eb9f3b00000000001fd37de0000000000002759c000000000000003d8000000000000000004b08000
noncomputable def e73n_target1 : Nat := 0xd0000000000000003c01000
noncomputable def e73n_target2 : Nat := 0x300201000
noncomputable def e73n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 234
  maxLength := 8
  maxWidth := 75
  terms := 1
  left := e73n_left
  right := e73n_right
  scale := e73n_scale
  target0 := e73n_target0
  target1 := e73n_target1
  target2 := e73n_target2

theorem e73n_ok : e73n.check=true := by decide +kernel
noncomputable def e73d_left_0 : Nat := 0xfceee18557a7676e00565d380000cf800000150000000002505000
noncomputable def e73d_left : Nat → Nat
  | 0 => e73d_left_0
  | _ => 0
noncomputable def e73d_right_0 : Nat := 0x300201000
noncomputable def e73d_right : Nat → Nat
  | 0 => e73d_right_0
  | _ => 0
noncomputable def e73d_scale : Nat := 0x18000000000002d01000
noncomputable def e73d_target0 : Nat := 0x7e7770c2a8007a7676e00000acba7000000033e000000000a8000000000003005000
noncomputable def e73d_target1 : Nat := 0x30000000002201000
noncomputable def e73d_target2 : Nat := 0x300201000
noncomputable def e73d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 150
  maxLength := 5
  maxWidth := 48
  terms := 1
  left := e73d_left
  right := e73d_right
  scale := e73d_scale
  target0 := e73d_target0
  target1 := e73d_target1
  target2 := e73d_target2

theorem e73d_ok : e73d.check=true := by decide +kernel
noncomputable def e74n_left_0 : Nat := 0x400357556c46b0e01b4522a024c01046daa7ba5000089feefda0000005e32c7400000003db8c0000000000db00000000000003907000
noncomputable def e74n_left : Nat → Nat
  | 0 => e74n_left_0
  | _ => 0
noncomputable def e74n_right_0 : Nat := 0x300201000
noncomputable def e74n_right : Nat → Nat
  | 0 => e74n_right_0
  | _ => 0
noncomputable def e74n_scale : Nat := 0x680000000000000003f01000
noncomputable def e74n_target0 : Nat := 0x1000d5d55b11ac300201b4522a024c0000411b6a9ee9400000089feefda00000000178cb1d00000000003db8c00000000000036c0000000000000004307000
noncomputable def e74n_target1 : Nat := 0x1a00000000000003501000
noncomputable def e74n_target2 : Nat := 0x300201000
noncomputable def e74n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 209
  maxLength := 7
  maxWidth := 67
  terms := 1
  left := e74n_left
  right := e74n_right
  scale := e74n_scale
  target0 := e74n_target0
  target1 := e74n_target1
  target2 := e74n_target2

theorem e74n_ok : e74n.check=true := by decide +kernel
noncomputable def e74d_left_0 : Nat := 0xfceee18557a7676e00565d380000cf800000150000000002505000
noncomputable def e74d_left : Nat → Nat
  | 0 => e74d_left_0
  | _ => 0
noncomputable def e74d_right_0 : Nat := 0x300201000
noncomputable def e74d_right : Nat → Nat
  | 0 => e74d_right_0
  | _ => 0
noncomputable def e74d_scale : Nat := 0x18000000000002d01000
noncomputable def e74d_target0 : Nat := 0x7e7770c2a8007a7676e00000acba7000000033e000000000a8000000000003005000
noncomputable def e74d_target1 : Nat := 0x30000000002201000
noncomputable def e74d_target2 : Nat := 0x300201000
noncomputable def e74d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 150
  maxLength := 5
  maxWidth := 48
  terms := 1
  left := e74d_left
  right := e74d_right
  scale := e74d_scale
  target0 := e74d_target0
  target1 := e74d_target1
  target2 := e74d_target2

theorem e74d_ok : e74d.check=true := by decide +kernel
noncomputable def e75n_left_0 : Nat := 0x10001826d829d0504fab8002e3551d03687c4003ffaf7ee24fb0350000202dd82ffe42f00000010137a85b5e20000000085318ae1c00000000004f8140500000000000030ba9000000000000000f0b000000000000000004d09000
noncomputable def e75n_left : Nat → Nat
  | 0 => e75n_left_0
  | _ => 0
noncomputable def e75n_right_0 : Nat := 0x300201000
noncomputable def e75n_right : Nat → Nat
  | 0 => e75n_right_0
  | _ => 0
noncomputable def e75n_scale : Nat := 0xd000000000000000000005001000
noncomputable def e75n_target0 : Nat := 0x4000609b60a741413eac008002e3551d03687c400000ffebdfb893ec0d4000000202dd82ffe42f000000000404dea16d788000000000085318ae1c00000000000013e050140000000000000030ba9000000000000000003c2c00000000000000000005709000
noncomputable def e75n_target1 : Nat := 0x34000000000000000004601000
noncomputable def e75n_target2 : Nat := 0x300201000
noncomputable def e75n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 270
  maxLength := 9
  maxWidth := 87
  terms := 1
  left := e75n_left
  right := e75n_right
  scale := e75n_scale
  target0 := e75n_target0
  target1 := e75n_target1
  target2 := e75n_target2

theorem e75n_ok : e75n.check=true := by decide +kernel
noncomputable def e75d_left_0 : Nat := 0xfceee18557a7676e00565d380000cf800000150000000002505000
noncomputable def e75d_left : Nat → Nat
  | 0 => e75d_left_0
  | _ => 0
noncomputable def e75d_right_0 : Nat := 0x300201000
noncomputable def e75d_right : Nat → Nat
  | 0 => e75d_right_0
  | _ => 0
noncomputable def e75d_scale : Nat := 0x30000000000002e01000
noncomputable def e75d_target0 : Nat := 0xfceee18550007a7676e00000565d380000000cf800000000150000000000003105000
noncomputable def e75d_target1 : Nat := 0x30000000002201000
noncomputable def e75d_target2 : Nat := 0x300201000
noncomputable def e75d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 153
  maxLength := 5
  maxWidth := 49
  terms := 1
  left := e75d_left
  right := e75d_right
  scale := e75d_scale
  target0 := e75d_target0
  target1 := e75d_target1
  target2 := e75d_target2

theorem e75d_ok : e75d.check=true := by decide +kernel
noncomputable def e76n_left_0 : Nat := 0x7ffe102a1dc994057fbee56da34a31007df5626b54010000786b51fcad00000053e48bbf000000000e276300000000005dfb0000000000007f0000000000000004008000
noncomputable def e76n_left : Nat → Nat
  | 0 => e76n_left_0
  | _ => 0
noncomputable def e76n_right_0 : Nat := 0x300201000
noncomputable def e76n_right : Nat → Nat
  | 0 => e76n_right_0
  | _ => 0
noncomputable def e76n_scale : Nat := 0x68000000000000000004701000
noncomputable def e76n_target0 : Nat := 0x7ffe102a1dc99405000ff7dcadb46946200001f7d589ad50040000003c35a8fe5680000000053e48bbf000000000001c4ec6000000000000177ec000000000000003f8000000000000000004b08000
noncomputable def e76n_target1 : Nat := 0xd0000000000000003c01000
noncomputable def e76n_target2 : Nat := 0x300201000
noncomputable def e76n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 234
  maxLength := 8
  maxWidth := 75
  terms := 1
  left := e76n_left
  right := e76n_right
  scale := e76n_scale
  target0 := e76n_target0
  target1 := e76n_target1
  target2 := e76n_target2

theorem e76n_ok : e76n.check=true := by decide +kernel
noncomputable def e76d_left_0 : Nat := 0xfceee18557a7676e00565d380000cf800000150000000002505000
noncomputable def e76d_left : Nat → Nat
  | 0 => e76d_left_0
  | _ => 0
noncomputable def e76d_right_0 : Nat := 0x300201000
noncomputable def e76d_right : Nat → Nat
  | 0 => e76d_right_0
  | _ => 0
noncomputable def e76d_scale : Nat := 0x18000000000002d01000
noncomputable def e76d_target0 : Nat := 0x7e7770c2a8007a7676e00000acba7000000033e000000000a8000000000003005000
noncomputable def e76d_target1 : Nat := 0x30000000002201000
noncomputable def e76d_target2 : Nat := 0x300201000
noncomputable def e76d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 150
  maxLength := 5
  maxWidth := 48
  terms := 1
  left := e76d_left
  right := e76d_right
  scale := e76d_scale
  target0 := e76d_target0
  target1 := e76d_target1
  target2 := e76d_target2

theorem e76d_ok : e76d.check=true := by decide +kernel
noncomputable def e77n_left_0 : Nat := 0x7ffee62a61a22512bfea3576a02264401fba8326f2e420000fb96e21c0d00000064389a8f80000000183a20c000000000236b60000000000011f0000000000000004108000
noncomputable def e77n_left : Nat → Nat
  | 0 => e77n_left_0
  | _ => 0
noncomputable def e77n_right_0 : Nat := 0x300201000
noncomputable def e77n_right : Nat → Nat
  | 0 => e77n_right_0
  | _ => 0
noncomputable def e77n_scale : Nat := 0x68000000000000000004701000
noncomputable def e77n_target0 : Nat := 0x7ffee62a61a225128007fd46aed4044c8800007eea0c9bcb9080000007dcb710e0680000000064389a8f8000000000030744180000000000008dad8000000000000008f8000000000000000004c08000
noncomputable def e77n_target1 : Nat := 0xd0000000000000003c01000
noncomputable def e77n_target2 : Nat := 0x300201000
noncomputable def e77n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 237
  maxLength := 8
  maxWidth := 76
  terms := 1
  left := e77n_left
  right := e77n_right
  scale := e77n_scale
  target0 := e77n_target0
  target1 := e77n_target1
  target2 := e77n_target2

theorem e77n_ok : e77n.check=true := by decide +kernel
noncomputable def e77d_left_0 : Nat := 0xfceee18557a7676e00565d380000cf800000150000000002505000
noncomputable def e77d_left : Nat → Nat
  | 0 => e77d_left_0
  | _ => 0
noncomputable def e77d_right_0 : Nat := 0x300201000
noncomputable def e77d_right : Nat → Nat
  | 0 => e77d_right_0
  | _ => 0
noncomputable def e77d_scale : Nat := 0x18000000000002d01000
noncomputable def e77d_target0 : Nat := 0x7e7770c2a8007a7676e00000acba7000000033e000000000a8000000000003005000
noncomputable def e77d_target1 : Nat := 0x30000000002201000
noncomputable def e77d_target2 : Nat := 0x300201000
noncomputable def e77d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 150
  maxLength := 5
  maxWidth := 48
  terms := 1
  left := e77d_left
  right := e77d_right
  scale := e77d_scale
  target0 := e77d_target0
  target1 := e77d_target1
  target2 := e77d_target2

theorem e77d_ok : e77d.check=true := by decide +kernel
noncomputable def e78n_left_0 : Nat := 0x100f91733b8094332004bce480003b88000001b0000000002505000
noncomputable def e78n_left : Nat → Nat
  | 0 => e78n_left_0
  | _ => 0
noncomputable def e78n_right_0 : Nat := 0x300201000
noncomputable def e78n_right : Nat → Nat
  | 0 => e78n_right_0
  | _ => 0
noncomputable def e78n_scale : Nat := 0x3000000000002a01000
noncomputable def e78n_target0 : Nat := 0x201f22e676008094332000025e724000000ee20000000036000000000002e05000
noncomputable def e78n_target1 : Nat := 0x18000000002101000
noncomputable def e78n_target2 : Nat := 0x300201000
noncomputable def e78n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 144
  maxLength := 5
  maxWidth := 46
  terms := 1
  left := e78n_left
  right := e78n_right
  scale := e78n_scale
  target0 := e78n_target0
  target1 := e78n_target1
  target2 := e78n_target2

theorem e78n_ok : e78n.check=true := by decide +kernel
noncomputable def e78d_left_0 : Nat := 0x54f0000a02000
noncomputable def e78d_left : Nat → Nat
  | 0 => e78d_left_0
  | _ => 0
noncomputable def e78d_right_0 : Nat := 0x300201000
noncomputable def e78d_right : Nat → Nat
  | 0 => e78d_right_0
  | _ => 0
noncomputable def e78d_scale : Nat := 0x3000001201000
noncomputable def e78d_target0 : Nat := 0x54c03000001202000
noncomputable def e78d_target1 : Nat := 0x30000a01000
noncomputable def e78d_target2 : Nat := 0x300201000
noncomputable def e78d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 57
  maxLength := 2
  maxWidth := 18
  terms := 1
  left := e78d_left
  right := e78d_right
  scale := e78d_scale
  target0 := e78d_target0
  target1 := e78d_target1
  target2 := e78d_target2

theorem e78d_ok : e78d.check=true := by decide +kernel
noncomputable def e79n_left_0 : Nat := 0x7ffcf28723a3c397fd0d57e9bf92007eb2f65cf3f000078cc09ddc0000005827ee7000000001ac7200000000003c100000000000003c07000
noncomputable def e79n_left : Nat → Nat
  | 0 => e79n_left_0
  | _ => 0
noncomputable def e79n_right_0 : Nat := 0x300201000
noncomputable def e79n_right : Nat → Nat
  | 0 => e79n_right_0
  | _ => 0
noncomputable def e79n_scale : Nat := 0xf80000000000000004001000
noncomputable def e79n_target0 : Nat := 0x7ffcf28723a3c39007fd0d57e9bf9200007eb2f65cf3f00000078cc09ddc000000005827ee700000000001ac720000000000003c10000000000000004407000
noncomputable def e79n_target1 : Nat := 0xf800000000000003801000
noncomputable def e79n_target2 : Nat := 0x300201000
noncomputable def e79n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 212
  maxLength := 7
  maxWidth := 68
  terms := 1
  left := e79n_left
  right := e79n_right
  scale := e79n_scale
  target0 := e79n_target0
  target1 := e79n_target1
  target2 := e79n_target2

theorem e79n_ok : e79n.check=true := by decide +kernel
noncomputable def e79d_left_0 : Nat := 0xfceee18557a7676e00565d380000cf800000150000000002505000
noncomputable def e79d_left : Nat → Nat
  | 0 => e79d_left_0
  | _ => 0
noncomputable def e79d_right_0 : Nat := 0x300201000
noncomputable def e79d_right : Nat → Nat
  | 0 => e79d_right_0
  | _ => 0
noncomputable def e79d_scale : Nat := 0x38000000000002e01000
noncomputable def e79d_target0 : Nat := 0xfb665247f80077b1b2500000618bd4000000037400000000178000000000003105000
noncomputable def e79d_target1 : Nat := 0x30000000002201000
noncomputable def e79d_target2 : Nat := 0x300201000
noncomputable def e79d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 153
  maxLength := 5
  maxWidth := 49
  terms := 1
  left := e79d_left
  right := e79d_right
  scale := e79d_scale
  target0 := e79d_target0
  target1 := e79d_target1
  target2 := e79d_target2

theorem e79d_ok : e79d.check=true := by decide +kernel
end ThomsonNegative.Certificate.Bridges.RFChecks
