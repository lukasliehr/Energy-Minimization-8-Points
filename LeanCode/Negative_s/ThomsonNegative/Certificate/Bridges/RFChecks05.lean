import ThomsonNegative.Structure.Packed.IdentityKernel
namespace ThomsonNegative.Certificate.Bridges.RFChecks
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
noncomputable def e50n_left_0 : Nat := 0x40040346c357f59952b800ef2923800014e7e0000001e50000000002b05000
noncomputable def e50n_left : Nat → Nat
  | 0 => e50n_left_0
  | _ => 0
noncomputable def e50n_right_0 : Nat := 0x300201000
noncomputable def e50n_right : Nat → Nat
  | 0 => e50n_right_0
  | _ => 0
noncomputable def e50n_scale : Nat := 0x798000000000003301000
noncomputable def e50n_target0 : Nat := 0x40040346c35007f59952b80000ef292380000014e7e000000001e5000000000003305000
noncomputable def e50n_target1 : Nat := 0x7980000000002b01000
noncomputable def e50n_target2 : Nat := 0x300201000
noncomputable def e50n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 159
  maxLength := 5
  maxWidth := 51
  terms := 1
  left := e50n_left
  right := e50n_right
  scale := e50n_scale
  target0 := e50n_target0
  target1 := e50n_target1
  target2 := e50n_target2

theorem e50n_ok : e50n.check=true := by decide +kernel
noncomputable def e50d_left_0 : Nat := 0x80126150b9d97f7aeb1e2f0071c20e6a00005502ae000000926d00000000f3000000000003006000
noncomputable def e50d_left : Nat → Nat
  | 0 => e50d_left_0
  | _ => 0
noncomputable def e50d_right_0 : Nat := 0x300201000
noncomputable def e50d_right : Nat → Nat
  | 0 => e50d_right_0
  | _ => 0
noncomputable def e50d_scale : Nat := 0x1800000000000003501000
noncomputable def e50d_target0 : Nat := 0x200498542e764003fbd758f178000071c20e6a0000000aa055c00000000249b4000000000079800000000000003b06000
noncomputable def e50d_target1 : Nat := 0x3000000000002a01000
noncomputable def e50d_target2 : Nat := 0x300201000
noncomputable def e50d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 184
  maxLength := 6
  maxWidth := 59
  terms := 1
  left := e50d_left
  right := e50d_right
  scale := e50d_scale
  target0 := e50d_target0
  target1 := e50d_target1
  target2 := e50d_target2

theorem e50d_ok : e50d.check=true := by decide +kernel
noncomputable def e51n_left_0 : Nat := 0x7ffe92981ca3dfec49086290081878f4980002857082000000cf46c0000000285000000000003206000
noncomputable def e51n_left : Nat → Nat
  | 0 => e51n_left_0
  | _ => 0
noncomputable def e51n_right_0 : Nat := 0x300201000
noncomputable def e51n_right : Nat → Nat
  | 0 => e51n_right_0
  | _ => 0
noncomputable def e51n_scale : Nat := 0x79800000000000003b01000
noncomputable def e51n_target0 : Nat := 0x1fffa4a60728f003fd89210c52000081878f49800000142b8410000000033d1b000000000050a00000000000003b06000
noncomputable def e51n_target1 : Nat := 0x3cc000000000003201000
noncomputable def e51n_target2 : Nat := 0x300201000
noncomputable def e51n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 184
  maxLength := 6
  maxWidth := 59
  terms := 1
  left := e51n_left
  right := e51n_right
  scale := e51n_scale
  target0 := e51n_target0
  target1 := e51n_target1
  target2 := e51n_target2

theorem e51n_ok : e51n.check=true := by decide +kernel
noncomputable def e51d_left_0 : Nat := 0x80126150b9d97f7aeb1e2f0071c20e6a00005502ae000000926d00000000f3000000000003006000
noncomputable def e51d_left : Nat → Nat
  | 0 => e51d_left_0
  | _ => 0
noncomputable def e51d_right_0 : Nat := 0x300201000
noncomputable def e51d_right : Nat → Nat
  | 0 => e51d_right_0
  | _ => 0
noncomputable def e51d_scale : Nat := 0x1800000000000003501000
noncomputable def e51d_target0 : Nat := 0x200498542e764003fbd758f178000071c20e6a0000000aa055c00000000249b4000000000079800000000000003b06000
noncomputable def e51d_target1 : Nat := 0x3000000000002a01000
noncomputable def e51d_target2 : Nat := 0x300201000
noncomputable def e51d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 184
  maxLength := 6
  maxWidth := 59
  terms := 1
  left := e51d_left
  right := e51d_right
  scale := e51d_scale
  target0 := e51d_target0
  target1 := e51d_target1
  target2 := e51d_target2

theorem e51d_ok : e51d.check=true := by decide +kernel
noncomputable def e52n_left_0 : Nat := 0x1ffc2fc12f6a7003bcc86c5008a6090c700005db97e8000003155e00000000b1000000000003106000
noncomputable def e52n_left : Nat → Nat
  | 0 => e52n_left_0
  | _ => 0
noncomputable def e52n_right_0 : Nat := 0x300201000
noncomputable def e52n_right : Nat → Nat
  | 0 => e52n_right_0
  | _ => 0
noncomputable def e52n_scale : Nat := 0x79800000000000003b01000
noncomputable def e52n_target0 : Nat := 0x1ffc2fc12f6a600400ef321b1400008a6090c7000000176e5fa000000003155e00000000002c400000000000003b06000
noncomputable def e52n_target1 : Nat := 0x1e6000000000003101000
noncomputable def e52n_target2 : Nat := 0x300201000
noncomputable def e52n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 184
  maxLength := 6
  maxWidth := 59
  terms := 1
  left := e52n_left
  right := e52n_right
  scale := e52n_scale
  target0 := e52n_target0
  target1 := e52n_target1
  target2 := e52n_target2

theorem e52n_ok : e52n.check=true := by decide +kernel
noncomputable def e52d_left_0 : Nat := 0x80126150b9d97f7aeb1e2f0071c20e6a00005502ae000000926d00000000f3000000000003006000
noncomputable def e52d_left : Nat → Nat
  | 0 => e52d_left_0
  | _ => 0
noncomputable def e52d_right_0 : Nat := 0x300201000
noncomputable def e52d_right : Nat → Nat
  | 0 => e52d_right_0
  | _ => 0
noncomputable def e52d_scale : Nat := 0x1800000000000003501000
noncomputable def e52d_target0 : Nat := 0x200498542e764003fbd758f178000071c20e6a0000000aa055c00000000249b4000000000079800000000000003b06000
noncomputable def e52d_target1 : Nat := 0x3000000000002a01000
noncomputable def e52d_target2 : Nat := 0x300201000
noncomputable def e52d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 184
  maxLength := 6
  maxWidth := 59
  terms := 1
  left := e52d_left
  right := e52d_right
  scale := e52d_scale
  target0 := e52d_target0
  target1 := e52d_target1
  target2 := e52d_target2

theorem e52d_ok : e52d.check=true := by decide +kernel
noncomputable def e53n_left_0 : Nat := 0x1fff9a3cf5a58dcf8012996bd751f80202e64e849790000821a979810000002220ba1100000000ae4a78000000000318700000000000003e07000
noncomputable def e53n_left : Nat → Nat
  | 0 => e53n_left_0
  | _ => 0
noncomputable def e53n_right_0 : Nat := 0x300201000
noncomputable def e53n_right : Nat → Nat
  | 0 => e53n_right_0
  | _ => 0
noncomputable def e53n_scale : Nat := 0xf300000000000000004401000
noncomputable def e53n_target0 : Nat := 0x1fff9a3cf5a58dcf008012996bd751f8000202e64e84979000000821a97981000000002220ba110000000000ae4a780000000000031870000000000000004607000
noncomputable def e53n_target1 : Nat := 0xf3000000000000003c01000
noncomputable def e53n_target2 : Nat := 0x300201000
noncomputable def e53n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 218
  maxLength := 7
  maxWidth := 70
  terms := 1
  left := e53n_left
  right := e53n_right
  scale := e53n_scale
  target0 := e53n_target0
  target1 := e53n_target1
  target2 := e53n_target2

theorem e53n_ok : e53n.check=true := by decide +kernel
noncomputable def e53d_left_0 : Nat := 0x80126150b9d97f7aeb1e2f0071c20e6a00005502ae000000926d00000000f3000000000003006000
noncomputable def e53d_left : Nat → Nat
  | 0 => e53d_left_0
  | _ => 0
noncomputable def e53d_right_0 : Nat := 0x300201000
noncomputable def e53d_right : Nat → Nat
  | 0 => e53d_right_0
  | _ => 0
noncomputable def e53d_scale : Nat := 0x3000000000000003601000
noncomputable def e53d_target0 : Nat := 0x80126150b9d90007f7aeb1e2f0000071c20e6a00000005502ae000000000926d00000000000f3000000000000003c06000
noncomputable def e53d_target1 : Nat := 0x3000000000002a01000
noncomputable def e53d_target2 : Nat := 0x300201000
noncomputable def e53d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 187
  maxLength := 6
  maxWidth := 60
  terms := 1
  left := e53d_left
  right := e53d_right
  scale := e53d_scale
  target0 := e53d_target0
  target1 := e53d_target1
  target2 := e53d_target2

theorem e53d_ok : e53d.check=true := by decide +kernel
noncomputable def e54n_left_0 : Nat := 0x7ffe2aec9f00298036bceb5af2007d24ccae4f00004af8011c00000000ddf70000000027d200000000003100000000000003807000
noncomputable def e54n_left : Nat → Nat
  | 0 => e54n_left_0
  | _ => 0
noncomputable def e54n_right_0 : Nat := 0x300201000
noncomputable def e54n_right : Nat → Nat
  | 0 => e54n_right_0
  | _ => 0
noncomputable def e54n_scale : Nat := 0x7980000000000000004301000
noncomputable def e54n_target0 : Nat := 0x1fff8abb27c00a4008036bceb5af200001f49332b93c0000004af8011c0000000000377dc000000000027d20000000000000c40000000000000004207000
noncomputable def e54n_target1 : Nat := 0x1e600000000000003901000
noncomputable def e54n_target2 : Nat := 0x300201000
noncomputable def e54n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 209
  maxLength := 7
  maxWidth := 67
  terms := 1
  left := e54n_left
  right := e54n_right
  scale := e54n_scale
  target0 := e54n_target0
  target1 := e54n_target1
  target2 := e54n_target2

theorem e54n_ok : e54n.check=true := by decide +kernel
noncomputable def e54d_left_0 : Nat := 0x80126150b9d97f7aeb1e2f0071c20e6a00005502ae000000926d00000000f3000000000003006000
noncomputable def e54d_left : Nat → Nat
  | 0 => e54d_left_0
  | _ => 0
noncomputable def e54d_right_0 : Nat := 0x300201000
noncomputable def e54d_right : Nat → Nat
  | 0 => e54d_right_0
  | _ => 0
noncomputable def e54d_scale : Nat := 0x1800000000000003501000
noncomputable def e54d_target0 : Nat := 0x200498542e764003fbd758f178000071c20e6a0000000aa055c00000000249b4000000000079800000000000003b06000
noncomputable def e54d_target1 : Nat := 0x3000000000002a01000
noncomputable def e54d_target2 : Nat := 0x300201000
noncomputable def e54d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 184
  maxLength := 6
  maxWidth := 59
  terms := 1
  left := e54d_left
  right := e54d_right
  scale := e54d_scale
  target0 := e54d_target0
  target1 := e54d_target1
  target2 := e54d_target2

theorem e54d_ok : e54d.check=true := by decide +kernel
noncomputable def e55n_left_0 : Nat := 0x10002bf7c8412b60047c8bf6fd003d2cea952b00003f549218000000005bcc0000000142d00000000001500000000000003707000
noncomputable def e55n_left : Nat → Nat
  | 0 => e55n_left_0
  | _ => 0
noncomputable def e55n_right_0 : Nat := 0x300201000
noncomputable def e55n_right : Nat → Nat
  | 0 => e55n_right_0
  | _ => 0
noncomputable def e55n_scale : Nat := 0x7980000000000000004301000
noncomputable def e55n_target0 : Nat := 0x200057ef9082568008011f22fdbf400001e96754a9580000003f54921800000000000b798000000000050b40000000000000a80000000000000004207000
noncomputable def e55n_target1 : Nat := 0xf300000000000003801000
noncomputable def e55n_target2 : Nat := 0x300201000
noncomputable def e55n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 209
  maxLength := 7
  maxWidth := 67
  terms := 1
  left := e55n_left
  right := e55n_right
  scale := e55n_scale
  target0 := e55n_target0
  target1 := e55n_target1
  target2 := e55n_target2

theorem e55n_ok : e55n.check=true := by decide +kernel
noncomputable def e55d_left_0 : Nat := 0x80126150b9d97f7aeb1e2f0071c20e6a00005502ae000000926d00000000f3000000000003006000
noncomputable def e55d_left : Nat → Nat
  | 0 => e55d_left_0
  | _ => 0
noncomputable def e55d_right_0 : Nat := 0x300201000
noncomputable def e55d_right : Nat → Nat
  | 0 => e55d_right_0
  | _ => 0
noncomputable def e55d_scale : Nat := 0x1800000000000003501000
noncomputable def e55d_target0 : Nat := 0x200498542e764003fbd758f178000071c20e6a0000000aa055c00000000249b4000000000079800000000000003b06000
noncomputable def e55d_target1 : Nat := 0x3000000000002a01000
noncomputable def e55d_target2 : Nat := 0x300201000
noncomputable def e55d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 184
  maxLength := 6
  maxWidth := 59
  terms := 1
  left := e55d_left
  right := e55d_right
  scale := e55d_scale
  target0 := e55d_target0
  target1 := e55d_target1
  target2 := e55d_target2

theorem e55d_ok : e55d.check=true := by decide +kernel
noncomputable def e56n_left_0 : Nat := 0x7fffd9245ee407c68c001df39a85d34340200233d465cfba0000fed793dc1990000007a4c66a31800000002c2726dc0000000000c6b5e000000000000ce30000000000000004508000
noncomputable def e56n_left : Nat → Nat
  | 0 => e56n_left_0
  | _ => 0
noncomputable def e56n_right_0 : Nat := 0x300201000
noncomputable def e56n_right : Nat → Nat
  | 0 => e56n_right_0
  | _ => 0
noncomputable def e56n_scale : Nat := 0xf30000000000000000004c01000
noncomputable def e56n_target0 : Nat := 0x7fffd9245ee407c68802000ef9cd42e9a1a00008008cf51973ee8000001fdaf27b8332000000007a4c66a3180000000001613936e00000000000031ad78000000000000019c6000000000000000004e08000
noncomputable def e56n_target1 : Nat := 0x7980000000000000004301000
noncomputable def e56n_target2 : Nat := 0x300201000
noncomputable def e56n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 243
  maxLength := 8
  maxWidth := 78
  terms := 1
  left := e56n_left
  right := e56n_right
  scale := e56n_scale
  target0 := e56n_target0
  target1 := e56n_target1
  target2 := e56n_target2

theorem e56n_ok : e56n.check=true := by decide +kernel
noncomputable def e56d_left_0 : Nat := 0x80126150b9d97f7aeb1e2f0071c20e6a00005502ae000000926d00000000f3000000000003006000
noncomputable def e56d_left : Nat → Nat
  | 0 => e56d_left_0
  | _ => 0
noncomputable def e56d_right_0 : Nat := 0x300201000
noncomputable def e56d_right : Nat → Nat
  | 0 => e56d_right_0
  | _ => 0
noncomputable def e56d_scale : Nat := 0x3000000000000003601000
noncomputable def e56d_target0 : Nat := 0x80126150b9d90007f7aeb1e2f0000071c20e6a00000005502ae000000000926d00000000000f3000000000000003c06000
noncomputable def e56d_target1 : Nat := 0x3000000000002a01000
noncomputable def e56d_target2 : Nat := 0x300201000
noncomputable def e56d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 187
  maxLength := 6
  maxWidth := 60
  terms := 1
  left := e56d_left
  right := e56d_right
  scale := e56d_scale
  target0 := e56d_target0
  target1 := e56d_target1
  target2 := e56d_target2

theorem e56d_ok : e56d.check=true := by decide +kernel
noncomputable def e57n_left_0 : Nat := 0x80008950835bf1a357ff91f0eea567a1007fbdee0d7907100008025d12b85d0000007c7a22b4f000000005050ab300000000002bfcb00000000000078f0000000000000004408000
noncomputable def e57n_left : Nat → Nat
  | 0 => e57n_left_0
  | _ => 0
noncomputable def e57n_right_0 : Nat := 0x300201000
noncomputable def e57n_right : Nat → Nat
  | 0 => e57n_right_0
  | _ => 0
noncomputable def e57n_scale : Nat := 0xf30000000000000000004c01000
noncomputable def e57n_target0 : Nat := 0x80008950835bf1a35001ffe47c3ba959e8400007fbdee0d790710000002009744ae174000000007c7a22b4f000000000014142acc0000000000002bfcb000000000000001e3c000000000000000004e08000
noncomputable def e57n_target1 : Nat := 0x3cc0000000000000004201000
noncomputable def e57n_target2 : Nat := 0x300201000
noncomputable def e57n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 243
  maxLength := 8
  maxWidth := 78
  terms := 1
  left := e57n_left
  right := e57n_right
  scale := e57n_scale
  target0 := e57n_target0
  target1 := e57n_target1
  target2 := e57n_target2

theorem e57n_ok : e57n.check=true := by decide +kernel
noncomputable def e57d_left_0 : Nat := 0x80126150b9d97f7aeb1e2f0071c20e6a00005502ae000000926d00000000f3000000000003006000
noncomputable def e57d_left : Nat → Nat
  | 0 => e57d_left_0
  | _ => 0
noncomputable def e57d_right_0 : Nat := 0x300201000
noncomputable def e57d_right : Nat → Nat
  | 0 => e57d_right_0
  | _ => 0
noncomputable def e57d_scale : Nat := 0x3000000000000003601000
noncomputable def e57d_target0 : Nat := 0x80126150b9d90007f7aeb1e2f0000071c20e6a00000005502ae000000000926d00000000000f3000000000000003c06000
noncomputable def e57d_target1 : Nat := 0x3000000000002a01000
noncomputable def e57d_target2 : Nat := 0x300201000
noncomputable def e57d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 187
  maxLength := 6
  maxWidth := 60
  terms := 1
  left := e57d_left
  right := e57d_right
  scale := e57d_scale
  target0 := e57d_target0
  target1 := e57d_target1
  target2 := e57d_target2

theorem e57d_ok : e57d.check=true := by decide +kernel
noncomputable def e58n_left_0 : Nat := 0x7ffe201a570b949bff04c5a1a071c020910b37ce6e0001392bbc2eb000000b442bc480000000450c140000000002dda00000000000190000000000000003d08000
noncomputable def e58n_left : Nat → Nat
  | 0 => e58n_left_0
  | _ => 0
noncomputable def e58n_right_0 : Nat := 0x300201000
noncomputable def e58n_right : Nat → Nat
  | 0 => e58n_right_0
  | _ => 0
noncomputable def e58n_scale : Nat := 0x798000000000000000004b01000
noncomputable def e58n_target0 : Nat := 0x7ffe201a570b9498000ffc13168681c70000020910b37ce6e00000004e4aef0bac000000000b442bc48000000000011430500000000000002dda000000000000000640000000000000000004b08000
noncomputable def e58n_target1 : Nat := 0x1e6000000000000003d01000
noncomputable def e58n_target2 : Nat := 0x300201000
noncomputable def e58n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 234
  maxLength := 8
  maxWidth := 75
  terms := 1
  left := e58n_left
  right := e58n_right
  scale := e58n_scale
  target0 := e58n_target0
  target1 := e58n_target1
  target2 := e58n_target2

theorem e58n_ok : e58n.check=true := by decide +kernel
noncomputable def e58d_left_0 : Nat := 0x80126150b9d97f7aeb1e2f0071c20e6a00005502ae000000926d00000000f3000000000003006000
noncomputable def e58d_left : Nat → Nat
  | 0 => e58d_left_0
  | _ => 0
noncomputable def e58d_right_0 : Nat := 0x300201000
noncomputable def e58d_right : Nat → Nat
  | 0 => e58d_right_0
  | _ => 0
noncomputable def e58d_scale : Nat := 0x1800000000000003501000
noncomputable def e58d_target0 : Nat := 0x200498542e764003fbd758f178000071c20e6a0000000aa055c00000000249b4000000000079800000000000003b06000
noncomputable def e58d_target1 : Nat := 0x3000000000002a01000
noncomputable def e58d_target2 : Nat := 0x300201000
noncomputable def e58d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 184
  maxLength := 6
  maxWidth := 59
  terms := 1
  left := e58d_left
  right := e58d_right
  scale := e58d_scale
  target0 := e58d_target0
  target1 := e58d_target1
  target2 := e58d_target2

theorem e58d_ok : e58d.check=true := by decide +kernel
noncomputable def e59n_left_0 : Nat := 0x7ffe60180f00530ddffb4aec1c6dc5b0081b366b4bb22c000255bbca1d2f000000b769d40d400000002b40d0100000000006c924000000000000350000000000000004208000
noncomputable def e59n_left : Nat → Nat
  | 0 => e59n_left_0
  | _ => 0
noncomputable def e59n_right_0 : Nat := 0x300201000
noncomputable def e59n_right : Nat → Nat
  | 0 => e59n_right_0
  | _ => 0
noncomputable def e59n_scale : Nat := 0x798000000000000000004b01000
noncomputable def e59n_target0 : Nat := 0x7ffe60180f00530dc007fed2bb071b716c000081b366b4bb22c000000956ef2874bc00000000b769d40d40000000000ad034040000000000006c924000000000000000d4000000000000000004c08000
noncomputable def e59n_target1 : Nat := 0x1e60000000000000004101000
noncomputable def e59n_target2 : Nat := 0x300201000
noncomputable def e59n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 237
  maxLength := 8
  maxWidth := 76
  terms := 1
  left := e59n_left
  right := e59n_right
  scale := e59n_scale
  target0 := e59n_target0
  target1 := e59n_target1
  target2 := e59n_target2

theorem e59n_ok : e59n.check=true := by decide +kernel
noncomputable def e59d_left_0 : Nat := 0x80126150b9d97f7aeb1e2f0071c20e6a00005502ae000000926d00000000f3000000000003006000
noncomputable def e59d_left : Nat → Nat
  | 0 => e59d_left_0
  | _ => 0
noncomputable def e59d_right_0 : Nat := 0x300201000
noncomputable def e59d_right : Nat → Nat
  | 0 => e59d_right_0
  | _ => 0
noncomputable def e59d_scale : Nat := 0x1800000000000003501000
noncomputable def e59d_target0 : Nat := 0x200498542e764003fbd758f178000071c20e6a0000000aa055c00000000249b4000000000079800000000000003b06000
noncomputable def e59d_target1 : Nat := 0x3000000000002a01000
noncomputable def e59d_target2 : Nat := 0x300201000
noncomputable def e59d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 184
  maxLength := 6
  maxWidth := 59
  terms := 1
  left := e59d_left
  right := e59d_right
  scale := e59d_scale
  target0 := e59d_target0
  target1 := e59d_target1
  target2 := e59d_target2

theorem e59d_ok : e59d.check=true := by decide +kernel
end ThomsonNegative.Certificate.Bridges.RFChecks
