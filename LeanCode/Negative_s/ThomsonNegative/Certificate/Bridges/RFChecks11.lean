import ThomsonNegative.Structure.Packed.IdentityKernel
namespace ThomsonNegative.Certificate.Bridges.RFChecks
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
noncomputable def e110n_left_0 : Nat := 0x200040cdb1825b824bf655e2580276bb1da0d0000e8b0cf500000037a405000000008cd80000000001300000000000003607000
noncomputable def e110n_left : Nat → Nat
  | 0 => e110n_left_0
  | _ => 0
noncomputable def e110n_right_0 : Nat := 0x300201000
noncomputable def e110n_right : Nat → Nat
  | 0 => e110n_right_0
  | _ => 0
noncomputable def e110n_scale : Nat := 0xf80000000000000004001000
noncomputable def e110n_target0 : Nat := 0x200040cdb1825b000824bf655e2580000276bb1da0d0000000e8b0cf500000000037a405000000000008cd80000000000001300000000000000004207000
noncomputable def e110n_target1 : Nat := 0xf80000000000003401000
noncomputable def e110n_target2 : Nat := 0x300201000
noncomputable def e110n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 206
  maxLength := 7
  maxWidth := 66
  terms := 1
  left := e110n_left
  right := e110n_right
  scale := e110n_scale
  target0 := e110n_target0
  target1 := e110n_target1
  target2 := e110n_target2

theorem e110n_ok : e110n.check=true := by decide +kernel
noncomputable def e110d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e110d_left : Nat → Nat
  | 0 => e110d_left_0
  | _ => 0
noncomputable def e110d_right_0 : Nat := 0x300201000
noncomputable def e110d_right : Nat → Nat
  | 0 => e110d_right_0
  | _ => 0
noncomputable def e110d_scale : Nat := 0x3800000000000003601000
noncomputable def e110d_target0 : Nat := 0x1fd04595aaad000f6038be7d800008d725dc80000004f090c000000000851000000000017800000000000003906000
noncomputable def e110d_target1 : Nat := 0x3000000000002a01000
noncomputable def e110d_target2 : Nat := 0x300201000
noncomputable def e110d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 178
  maxLength := 6
  maxWidth := 57
  terms := 1
  left := e110d_left
  right := e110d_right
  scale := e110d_scale
  target0 := e110d_target0
  target1 := e110d_target1
  target2 := e110d_target2

theorem e110d_ok : e110d.check=true := by decide +kernel
noncomputable def e111n_left_0 : Nat := 0x643a1376001000001403000
noncomputable def e111n_left : Nat → Nat
  | 0 => e111n_left_0
  | _ => 0
noncomputable def e111n_right_0 : Nat := 0x300201000
noncomputable def e111n_right : Nat → Nat
  | 0 => e111n_right_0
  | _ => 0
noncomputable def e111n_scale : Nat := 0x700000001b01000
noncomputable def e111n_target0 : Nat := 0x321d0800dd80000200000001d03000
noncomputable def e111n_target1 : Nat := 0x3800001201000
noncomputable def e111n_target2 : Nat := 0x300201000
noncomputable def e111n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 91
  maxLength := 3
  maxWidth := 29
  terms := 1
  left := e111n_left
  right := e111n_right
  scale := e111n_scale
  target0 := e111n_target0
  target1 := e111n_target1
  target2 := e111n_target2

theorem e111n_ok : e111n.check=true := by decide +kernel
noncomputable def e111d_left_0 : Nat := 0x54f0000a02000
noncomputable def e111d_left : Nat → Nat
  | 0 => e111d_left_0
  | _ => 0
noncomputable def e111d_right_0 : Nat := 0x300201000
noncomputable def e111d_right : Nat → Nat
  | 0 => e111d_right_0
  | _ => 0
noncomputable def e111d_scale : Nat := 0x7000001301000
noncomputable def e111d_target0 : Nat := 0xfc807000001302000
noncomputable def e111d_target1 : Nat := 0x30000a01000
noncomputable def e111d_target2 : Nat := 0x300201000
noncomputable def e111d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 60
  maxLength := 2
  maxWidth := 19
  terms := 1
  left := e111d_left
  right := e111d_right
  scale := e111d_scale
  target0 := e111d_target0
  target1 := e111d_target1
  target2 := e111d_target2

theorem e111d_ok : e111d.check=true := by decide +kernel
noncomputable def e112n_left_0 : Nat := 0x2007e9c621504c13f44bd47f0094a56829400018f9a938000003c82e80000000583000000000003306000
noncomputable def e112n_left : Nat → Nat
  | 0 => e112n_left_0
  | _ => 0
noncomputable def e112n_right_0 : Nat := 0x300201000
noncomputable def e112n_right : Nat → Nat
  | 0 => e112n_right_0
  | _ => 0
noncomputable def e112n_scale : Nat := 0x36800000000000003a01000
noncomputable def e112n_target0 : Nat := 0x2007e9c62150480413f44bd47f000094a5682940000018f9a93800000003c82e800000000058300000000000003b06000
noncomputable def e112n_target1 : Nat := 0x368000000000003201000
noncomputable def e112n_target2 : Nat := 0x300201000
noncomputable def e112n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 184
  maxLength := 6
  maxWidth := 59
  terms := 1
  left := e112n_left
  right := e112n_right
  scale := e112n_scale
  target0 := e112n_target0
  target1 := e112n_target1
  target2 := e112n_target2

theorem e112n_ok : e112n.check=true := by decide +kernel
noncomputable def e112d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e112d_left : Nat → Nat
  | 0 => e112d_left_0
  | _ => 0
noncomputable def e112d_right_0 : Nat := 0x300201000
noncomputable def e112d_right : Nat → Nat
  | 0 => e112d_right_0
  | _ => 0
noncomputable def e112d_scale : Nat := 0xc800000000000003801000
noncomputable def e112d_target0 : Nat := 0x1fdc34304001c003e20aa3b78800008a15c65600000012d1b24000000000e3cc000000000056800000000000003b06000
noncomputable def e112d_target1 : Nat := 0x3000000000002a01000
noncomputable def e112d_target2 : Nat := 0x300201000
noncomputable def e112d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 184
  maxLength := 6
  maxWidth := 59
  terms := 1
  left := e112d_left
  right := e112d_right
  scale := e112d_scale
  target0 := e112d_target0
  target1 := e112d_target1
  target2 := e112d_target2

theorem e112d_ok : e112d.check=true := by decide +kernel
noncomputable def e113n_left_0 : Nat := 0x1ffdb957a90ece37e9de71d5de9801c7bf503445000046346e6d000000022387d00000000295180000000001bb00000000000003a07000
noncomputable def e113n_left : Nat → Nat
  | 0 => e113n_left_0
  | _ => 0
noncomputable def e113n_right_0 : Nat := 0x300201000
noncomputable def e113n_right : Nat → Nat
  | 0 => e113n_right_0
  | _ => 0
noncomputable def e113n_scale : Nat := 0x3680000000000000004201000
noncomputable def e113n_target0 : Nat := 0xffedcabd487671801fa779c7577a6000038f7ea0688a00000046346e6d000000000111c3e80000000000a5460000000000003760000000000000004307000
noncomputable def e113n_target1 : Nat := 0x1b400000000000003901000
noncomputable def e113n_target2 : Nat := 0x300201000
noncomputable def e113n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 209
  maxLength := 7
  maxWidth := 67
  terms := 1
  left := e113n_left
  right := e113n_right
  scale := e113n_scale
  target0 := e113n_target0
  target1 := e113n_target1
  target2 := e113n_target2

theorem e113n_ok : e113n.check=true := by decide +kernel
noncomputable def e113d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e113d_left : Nat → Nat
  | 0 => e113d_left_0
  | _ => 0
noncomputable def e113d_right_0 : Nat := 0x300201000
noncomputable def e113d_right : Nat → Nat
  | 0 => e113d_right_0
  | _ => 0
noncomputable def e113d_scale : Nat := 0xc800000000000003801000
noncomputable def e113d_target0 : Nat := 0x1fdc34304001c003e20aa3b78800008a15c65600000012d1b24000000000e3cc000000000056800000000000003b06000
noncomputable def e113d_target1 : Nat := 0x3000000000002a01000
noncomputable def e113d_target2 : Nat := 0x300201000
noncomputable def e113d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 184
  maxLength := 6
  maxWidth := 59
  terms := 1
  left := e113d_left
  right := e113d_right
  scale := e113d_scale
  target0 := e113d_target0
  target1 := e113d_target1
  target2 := e113d_target2

theorem e113d_ok : e113d.check=true := by decide +kernel
noncomputable def e114n_left_0 : Nat := 0x3ffd253776abd65fce038c4b46400ee785635bf000059762b8e0000001ee4c1c00000001cd2400000000010100000000000003907000
noncomputable def e114n_left : Nat → Nat
  | 0 => e114n_left_0
  | _ => 0
noncomputable def e114n_right_0 : Nat := 0x300201000
noncomputable def e114n_right : Nat → Nat
  | 0 => e114n_right_0
  | _ => 0
noncomputable def e114n_scale : Nat := 0x3680000000000000004201000
noncomputable def e114n_target0 : Nat := 0x7ffa4a6eed57ac8007f380e312d1900000773c2b1adf800000059762b8e0000000003dc98380000000000734900000000000008080000000000000004407000
noncomputable def e114n_target1 : Nat := 0x6d00000000000003701000
noncomputable def e114n_target2 : Nat := 0x300201000
noncomputable def e114n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 212
  maxLength := 7
  maxWidth := 68
  terms := 1
  left := e114n_left
  right := e114n_right
  scale := e114n_scale
  target0 := e114n_target0
  target1 := e114n_target1
  target2 := e114n_target2

theorem e114n_ok : e114n.check=true := by decide +kernel
noncomputable def e114d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e114d_left : Nat → Nat
  | 0 => e114d_left_0
  | _ => 0
noncomputable def e114d_right_0 : Nat := 0x300201000
noncomputable def e114d_right : Nat → Nat
  | 0 => e114d_right_0
  | _ => 0
noncomputable def e114d_scale : Nat := 0xc800000000000003801000
noncomputable def e114d_target0 : Nat := 0x1fdc34304001c003e20aa3b78800008a15c65600000012d1b24000000000e3cc000000000056800000000000003b06000
noncomputable def e114d_target1 : Nat := 0x3000000000002a01000
noncomputable def e114d_target2 : Nat := 0x300201000
noncomputable def e114d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 184
  maxLength := 6
  maxWidth := 59
  terms := 1
  left := e114d_left
  right := e114d_right
  scale := e114d_scale
  target0 := e114d_target0
  target1 := e114d_target1
  target2 := e114d_target2

theorem e114d_ok : e114d.check=true := by decide +kernel
noncomputable def e115n_left_0 : Nat := 0x8d717d5a007000001403000
noncomputable def e115n_left : Nat → Nat
  | 0 => e115n_left_0
  | _ => 0
noncomputable def e115n_right_0 : Nat := 0x300201000
noncomputable def e115n_right : Nat → Nat
  | 0 => e115n_right_0
  | _ => 0
noncomputable def e115n_scale : Nat := 0x1900000001d01000
noncomputable def e115n_target0 : Nat := 0x46b8b8035680000e00000001d03000
noncomputable def e115n_target1 : Nat := 0xc800001401000
noncomputable def e115n_target2 : Nat := 0x300201000
noncomputable def e115n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 91
  maxLength := 3
  maxWidth := 29
  terms := 1
  left := e115n_left
  right := e115n_right
  scale := e115n_scale
  target0 := e115n_target0
  target1 := e115n_target1
  target2 := e115n_target2

theorem e115n_ok : e115n.check=true := by decide +kernel
noncomputable def e115d_left_0 : Nat := 0x54f0000a02000
noncomputable def e115d_left : Nat → Nat
  | 0 => e115d_left_0
  | _ => 0
noncomputable def e115d_right_0 : Nat := 0x300201000
noncomputable def e115d_right : Nat → Nat
  | 0 => e115d_right_0
  | _ => 0
noncomputable def e115d_scale : Nat := 0x19000001501000
noncomputable def e115d_target0 : Nat := 0x13d6019000001502000
noncomputable def e115d_target1 : Nat := 0x30000a01000
noncomputable def e115d_target2 : Nat := 0x300201000
noncomputable def e115d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 66
  maxLength := 2
  maxWidth := 21
  terms := 1
  left := e115d_left
  right := e115d_right
  scale := e115d_scale
  target0 := e115d_target0
  target1 := e115d_target1
  target2 := e115d_target2

theorem e115d_ok : e115d.check=true := by decide +kernel
noncomputable def e116n_left_0 : Nat := 0x3ffc7c056fb803df7dc8010cd86480002b0a200000064b0000000002b05000
noncomputable def e116n_left : Nat → Nat
  | 0 => e116n_left_0
  | _ => 0
noncomputable def e116n_right_0 : Nat := 0x300201000
noncomputable def e116n_right : Nat → Nat
  | 0 => e116n_right_0
  | _ => 0
noncomputable def e116n_scale : Nat := 0x34000000000002e01000
noncomputable def e116n_target0 : Nat := 0x3ffc7c056fb00803df7dc800010cd8648000002b0a20000000064b000000000003305000
noncomputable def e116n_target1 : Nat := 0x340000000002601000
noncomputable def e116n_target2 : Nat := 0x300201000
noncomputable def e116n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 159
  maxLength := 5
  maxWidth := 51
  terms := 1
  left := e116n_left
  right := e116n_right
  scale := e116n_scale
  target0 := e116n_target0
  target1 := e116n_target1
  target2 := e116n_target2

theorem e116n_ok : e116n.check=true := by decide +kernel
noncomputable def e116d_left_0 : Nat := 0xfceee18557a7676e00565d380000cf800000150000000002505000
noncomputable def e116d_left : Nat → Nat
  | 0 => e116d_left_0
  | _ => 0
noncomputable def e116d_right_0 : Nat := 0x300201000
noncomputable def e116d_right : Nat → Nat
  | 0 => e116d_right_0
  | _ => 0
noncomputable def e116d_scale : Nat := 0xc000000000002c01000
noncomputable def e116d_target0 : Nat := 0x3f3bb86154007a7676e000015974e0000000cf80000000054000000000002f05000
noncomputable def e116d_target1 : Nat := 0x30000000002201000
noncomputable def e116d_target2 : Nat := 0x300201000
noncomputable def e116d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 147
  maxLength := 5
  maxWidth := 47
  terms := 1
  left := e116d_left
  right := e116d_right
  scale := e116d_scale
  target0 := e116d_target0
  target1 := e116d_target1
  target2 := e116d_target2

theorem e116d_ok : e116d.check=true := by decide +kernel
noncomputable def e117n_left_0 : Nat := 0x8001bff34c6e600b7f4c1cf007d6a3d4a800017249ee000000327340000000193000000000003206000
noncomputable def e117n_left : Nat → Nat
  | 0 => e117n_left_0
  | _ => 0
noncomputable def e117n_right_0 : Nat := 0x300201000
noncomputable def e117n_right : Nat → Nat
  | 0 => e117n_right_0
  | _ => 0
noncomputable def e117n_scale : Nat := 0x3400000000000003601000
noncomputable def e117n_target0 : Nat := 0x20006ffcd31b9004016fe9839e00007d6a3d4a8000000b924f7000000000c9cd000000000032600000000000003b06000
noncomputable def e117n_target1 : Nat := 0x1a000000000002d01000
noncomputable def e117n_target2 : Nat := 0x300201000
noncomputable def e117n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 184
  maxLength := 6
  maxWidth := 59
  terms := 1
  left := e117n_left
  right := e117n_right
  scale := e117n_scale
  target0 := e117n_target0
  target1 := e117n_target1
  target2 := e117n_target2

theorem e117n_ok : e117n.check=true := by decide +kernel
noncomputable def e117d_left_0 : Nat := 0xfceee18557a7676e00565d380000cf800000150000000002505000
noncomputable def e117d_left : Nat → Nat
  | 0 => e117d_left_0
  | _ => 0
noncomputable def e117d_right_0 : Nat := 0x300201000
noncomputable def e117d_right : Nat → Nat
  | 0 => e117d_right_0
  | _ => 0
noncomputable def e117d_scale : Nat := 0xc000000000002c01000
noncomputable def e117d_target0 : Nat := 0x3f3bb86154007a7676e000015974e0000000cf80000000054000000000002f05000
noncomputable def e117d_target1 : Nat := 0x30000000002201000
noncomputable def e117d_target2 : Nat := 0x300201000
noncomputable def e117d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 147
  maxLength := 5
  maxWidth := 47
  terms := 1
  left := e117d_left
  right := e117d_right
  scale := e117d_scale
  target0 := e117d_target0
  target1 := e117d_target1
  target2 := e117d_target2

theorem e117d_ok : e117d.check=true := by decide +kernel
noncomputable def e118n_left_0 : Nat := 0x200196fa08ecc004ce36bf007a84d6540000a3fc38000000c968000000043000000000002f06000
noncomputable def e118n_left : Nat → Nat
  | 0 => e118n_left_0
  | _ => 0
noncomputable def e118n_right_0 : Nat := 0x300201000
noncomputable def e118n_right : Nat → Nat
  | 0 => e118n_right_0
  | _ => 0
noncomputable def e118n_scale : Nat := 0x3400000000000003601000
noncomputable def e118n_target0 : Nat := 0x200196fa08ec8004004ce36bf000007a84d6540000000a3fc38000000000c968000000000043000000000000003b06000
noncomputable def e118n_target1 : Nat := 0x3400000000002a01000
noncomputable def e118n_target2 : Nat := 0x300201000
noncomputable def e118n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 184
  maxLength := 6
  maxWidth := 59
  terms := 1
  left := e118n_left
  right := e118n_right
  scale := e118n_scale
  target0 := e118n_target0
  target1 := e118n_target1
  target2 := e118n_target2

theorem e118n_ok : e118n.check=true := by decide +kernel
noncomputable def e118d_left_0 : Nat := 0xfceee18557a7676e00565d380000cf800000150000000002505000
noncomputable def e118d_left : Nat → Nat
  | 0 => e118d_left_0
  | _ => 0
noncomputable def e118d_right_0 : Nat := 0x300201000
noncomputable def e118d_right : Nat → Nat
  | 0 => e118d_right_0
  | _ => 0
noncomputable def e118d_scale : Nat := 0xc000000000002c01000
noncomputable def e118d_target0 : Nat := 0x3f3bb86154007a7676e000015974e0000000cf80000000054000000000002f05000
noncomputable def e118d_target1 : Nat := 0x30000000002201000
noncomputable def e118d_target2 : Nat := 0x300201000
noncomputable def e118d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 147
  maxLength := 5
  maxWidth := 47
  terms := 1
  left := e118d_left
  right := e118d_right
  scale := e118d_scale
  target0 := e118d_target0
  target1 := e118d_target1
  target2 := e118d_target2

theorem e118d_ok : e118d.check=true := by decide +kernel
noncomputable def e119n_left_0 : Nat := 0x200033e83176d1157ff4ca136f572801fec3c8c058300008036b3e5b0000001ee5738b000000004d2ca80000000000b7d00000000000003e07000
noncomputable def e119n_left : Nat → Nat
  | 0 => e119n_left_0
  | _ => 0
noncomputable def e119n_right_0 : Nat := 0x300201000
noncomputable def e119n_right : Nat → Nat
  | 0 => e119n_right_0
  | _ => 0
noncomputable def e119n_scale : Nat := 0x680000000000000003f01000
noncomputable def e119n_target0 : Nat := 0x200033e83176d115007ff4ca136f57280001fec3c8c05830000008036b3e5b000000001ee5738b00000000004d2ca8000000000000b7d0000000000000004607000
noncomputable def e119n_target1 : Nat := 0x6800000000000003701000
noncomputable def e119n_target2 : Nat := 0x300201000
noncomputable def e119n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 218
  maxLength := 7
  maxWidth := 70
  terms := 1
  left := e119n_left
  right := e119n_right
  scale := e119n_scale
  target0 := e119n_target0
  target1 := e119n_target1
  target2 := e119n_target2

theorem e119n_ok : e119n.check=true := by decide +kernel
noncomputable def e119d_left_0 : Nat := 0xfceee18557a7676e00565d380000cf800000150000000002505000
noncomputable def e119d_left : Nat → Nat
  | 0 => e119d_left_0
  | _ => 0
noncomputable def e119d_right_0 : Nat := 0x300201000
noncomputable def e119d_right : Nat → Nat
  | 0 => e119d_right_0
  | _ => 0
noncomputable def e119d_scale : Nat := 0x18000000000002d01000
noncomputable def e119d_target0 : Nat := 0x7e7770c2a8007a7676e00000acba7000000033e000000000a8000000000003005000
noncomputable def e119d_target1 : Nat := 0x30000000002201000
noncomputable def e119d_target2 : Nat := 0x300201000
noncomputable def e119d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 150
  maxLength := 5
  maxWidth := 48
  terms := 1
  left := e119d_left
  right := e119d_right
  scale := e119d_scale
  target0 := e119d_target0
  target1 := e119d_target1
  target2 := e119d_target2

theorem e119d_ok : e119d.check=true := by decide +kernel
end ThomsonNegative.Certificate.Bridges.RFChecks
