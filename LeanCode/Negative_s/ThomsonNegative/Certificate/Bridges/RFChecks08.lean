import ThomsonNegative.Structure.Packed.IdentityKernel
namespace ThomsonNegative.Certificate.Bridges.RFChecks
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
noncomputable def e80n_left_0 : Nat := 0x8000dd20562ff1957003e7f8ef41bdfc0203f66ac3583780004227975f3c30000009c99db8a200000001bd306b40000000003806a8000000000004d10000000000000004308000
noncomputable def e80n_left : Nat → Nat
  | 0 => e80n_left_0
  | _ => 0
noncomputable def e80n_right_0 : Nat := 0x300201000
noncomputable def e80n_right : Nat → Nat
  | 0 => e80n_right_0
  | _ => 0
noncomputable def e80n_scale : Nat := 0xf8000000000000000004801000
noncomputable def e80n_target0 : Nat := 0x8000dd20562ff195600801f3fc77a0defe000080fd9ab0d60de000000844f2ebe786000000009c99db8a20000000000de9835a000000000000e01aa000000000000009a2000000000000000004c08000
noncomputable def e80n_target1 : Nat := 0x7c0000000000000003f01000
noncomputable def e80n_target2 : Nat := 0x300201000
noncomputable def e80n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 237
  maxLength := 8
  maxWidth := 76
  terms := 1
  left := e80n_left
  right := e80n_right
  scale := e80n_scale
  target0 := e80n_target0
  target1 := e80n_target1
  target2 := e80n_target2

theorem e80n_ok : e80n.check=true := by decide +kernel
noncomputable def e80d_left_0 : Nat := 0xfceee18557a7676e00565d380000cf800000150000000002505000
noncomputable def e80d_left : Nat → Nat
  | 0 => e80d_left_0
  | _ => 0
noncomputable def e80d_right_0 : Nat := 0x300201000
noncomputable def e80d_right : Nat → Nat
  | 0 => e80d_right_0
  | _ => 0
noncomputable def e80d_scale : Nat := 0x38000000000002e01000
noncomputable def e80d_target0 : Nat := 0xfb665247f80077b1b2500000618bd4000000037400000000178000000000003105000
noncomputable def e80d_target1 : Nat := 0x30000000002201000
noncomputable def e80d_target2 : Nat := 0x300201000
noncomputable def e80d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 153
  maxLength := 5
  maxWidth := 49
  terms := 1
  left := e80d_left
  right := e80d_right
  scale := e80d_scale
  target0 := e80d_target0
  target1 := e80d_target1
  target2 := e80d_target2

theorem e80d_ok : e80d.check=true := by decide +kernel
noncomputable def e81n_left_0 : Nat := 0x80014d01fea6b4ce6008a6940af4615008102cf22206940002149f4b6b01000000a8297506c00000003caee4f0000000000bdf1c000000000001db0000000000000004208000
noncomputable def e81n_left : Nat → Nat
  | 0 => e81n_left_0
  | _ => 0
noncomputable def e81n_right_0 : Nat := 0x300201000
noncomputable def e81n_right : Nat → Nat
  | 0 => e81n_right_0
  | _ => 0
noncomputable def e81n_scale : Nat := 0xf8000000000000000004801000
noncomputable def e81n_target0 : Nat := 0x80014d01fea6b4ce40080229a502bd185400008102cf22206940000008527d2dac0400000000a8297506c0000000000f2bb93c000000000000bdf1c0000000000000076c000000000000000004c08000
noncomputable def e81n_target1 : Nat := 0x3e0000000000000003e01000
noncomputable def e81n_target2 : Nat := 0x300201000
noncomputable def e81n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 237
  maxLength := 8
  maxWidth := 76
  terms := 1
  left := e81n_left
  right := e81n_right
  scale := e81n_scale
  target0 := e81n_target0
  target1 := e81n_target1
  target2 := e81n_target2

theorem e81n_ok : e81n.check=true := by decide +kernel
noncomputable def e81d_left_0 : Nat := 0xfceee18557a7676e00565d380000cf800000150000000002505000
noncomputable def e81d_left : Nat → Nat
  | 0 => e81d_left_0
  | _ => 0
noncomputable def e81d_right_0 : Nat := 0x300201000
noncomputable def e81d_right : Nat → Nat
  | 0 => e81d_right_0
  | _ => 0
noncomputable def e81d_scale : Nat := 0x38000000000002e01000
noncomputable def e81d_target0 : Nat := 0xfb665247f80077b1b2500000618bd4000000037400000000178000000000003105000
noncomputable def e81d_target1 : Nat := 0x30000000002201000
noncomputable def e81d_target2 : Nat := 0x300201000
noncomputable def e81d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 153
  maxLength := 5
  maxWidth := 49
  terms := 1
  left := e81d_left
  right := e81d_right
  scale := e81d_scale
  target0 := e81d_target0
  target1 := e81d_target1
  target2 := e81d_target2

theorem e81d_ok : e81d.check=true := by decide +kernel
noncomputable def e82n_left_0 : Nat := 0xfe8556aab7ad3212002c26c80000508000000b0000000002505000
noncomputable def e82n_left : Nat → Nat
  | 0 => e82n_left_0
  | _ => 0
noncomputable def e82n_right_0 : Nat := 0x300201000
noncomputable def e82n_right : Nat → Nat
  | 0 => e82n_right_0
  | _ => 0
noncomputable def e82n_scale : Nat := 0x7000000000002b01000
noncomputable def e82n_target0 : Nat := 0xfe8556aab007ad321200002c26c800000050800000000b000000000002d05000
noncomputable def e82n_target1 : Nat := 0x70000000002301000
noncomputable def e82n_target2 : Nat := 0x300201000
noncomputable def e82n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 141
  maxLength := 5
  maxWidth := 45
  terms := 1
  left := e82n_left
  right := e82n_right
  scale := e82n_scale
  target0 := e82n_target0
  target1 := e82n_target1
  target2 := e82n_target2

theorem e82n_ok : e82n.check=true := by decide +kernel
noncomputable def e82d_left_0 : Nat := 0x54f0000a02000
noncomputable def e82d_left : Nat → Nat
  | 0 => e82d_left_0
  | _ => 0
noncomputable def e82d_right_0 : Nat := 0x300201000
noncomputable def e82d_right : Nat → Nat
  | 0 => e82d_right_0
  | _ => 0
noncomputable def e82d_scale : Nat := 0x7000001301000
noncomputable def e82d_target0 : Nat := 0xfc807000001302000
noncomputable def e82d_target1 : Nat := 0x30000a01000
noncomputable def e82d_target2 : Nat := 0x300201000
noncomputable def e82d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 60
  maxLength := 2
  maxWidth := 19
  terms := 1
  left := e82d_left
  right := e82d_right
  scale := e82d_scale
  target0 := e82d_target0
  target1 := e82d_target1
  target2 := e82d_target2

theorem e82d_ok : e82d.check=true := by decide +kernel
noncomputable def e83n_left_0 : Nat := 0x20008c427e71e2ff81427cbd7007e8d08fed00003912a5f80000001acca0000000077b000000000003506000
noncomputable def e83n_left : Nat → Nat
  | 0 => e83n_left_0
  | _ => 0
noncomputable def e83n_right_0 : Nat := 0x300201000
noncomputable def e83n_right : Nat → Nat
  | 0 => e83n_right_0
  | _ => 0
noncomputable def e83n_scale : Nat := 0xf800000000000003801000
noncomputable def e83n_target0 : Nat := 0x20008c427e71e200ff81427cbd700007e8d08fed0000003912a5f8000000001acca000000000077b00000000000003d06000
noncomputable def e83n_target1 : Nat := 0xf8000000000003001000
noncomputable def e83n_target2 : Nat := 0x300201000
noncomputable def e83n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 190
  maxLength := 6
  maxWidth := 61
  terms := 1
  left := e83n_left
  right := e83n_right
  scale := e83n_scale
  target0 := e83n_target0
  target1 := e83n_target1
  target2 := e83n_target2

theorem e83n_ok : e83n.check=true := by decide +kernel
noncomputable def e83d_left_0 : Nat := 0xfceee18557a7676e00565d380000cf800000150000000002505000
noncomputable def e83d_left : Nat → Nat
  | 0 => e83d_left_0
  | _ => 0
noncomputable def e83d_right_0 : Nat := 0x300201000
noncomputable def e83d_right : Nat → Nat
  | 0 => e83d_right_0
  | _ => 0
noncomputable def e83d_scale : Nat := 0x38000000000002e01000
noncomputable def e83d_target0 : Nat := 0xfb665247f80077b1b2500000618bd4000000037400000000178000000000003105000
noncomputable def e83d_target1 : Nat := 0x30000000002201000
noncomputable def e83d_target2 : Nat := 0x300201000
noncomputable def e83d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 153
  maxLength := 5
  maxWidth := 49
  terms := 1
  left := e83d_left
  right := e83d_right
  scale := e83d_scale
  target0 := e83d_target0
  target1 := e83d_target1
  target2 := e83d_target2

theorem e83d_ok : e83d.check=true := by decide +kernel
noncomputable def e84n_left_0 : Nat := 0x80031b456dacf6b803ebf2a674b6008060076a87d0000834b94b94000000e9618f500000000e5d56000000000098300000000000003c07000
noncomputable def e84n_left : Nat → Nat
  | 0 => e84n_left_0
  | _ => 0
noncomputable def e84n_right_0 : Nat := 0x300201000
noncomputable def e84n_right : Nat → Nat
  | 0 => e84n_right_0
  | _ => 0
noncomputable def e84n_scale : Nat := 0xf80000000000000004001000
noncomputable def e84n_target0 : Nat := 0x40018da2b6d67b580200fafca99d2d8000100c00ed50fa000000834b94b940000000074b0c7a80000000003975580000000000013060000000000000004507000
noncomputable def e84n_target1 : Nat := 0x7c00000000000003701000
noncomputable def e84n_target2 : Nat := 0x300201000
noncomputable def e84n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 215
  maxLength := 7
  maxWidth := 69
  terms := 1
  left := e84n_left
  right := e84n_right
  scale := e84n_scale
  target0 := e84n_target0
  target1 := e84n_target1
  target2 := e84n_target2

theorem e84n_ok : e84n.check=true := by decide +kernel
noncomputable def e84d_left_0 : Nat := 0xfceee18557a7676e00565d380000cf800000150000000002505000
noncomputable def e84d_left : Nat → Nat
  | 0 => e84d_left_0
  | _ => 0
noncomputable def e84d_right_0 : Nat := 0x300201000
noncomputable def e84d_right : Nat → Nat
  | 0 => e84d_right_0
  | _ => 0
noncomputable def e84d_scale : Nat := 0x38000000000002e01000
noncomputable def e84d_target0 : Nat := 0xfb665247f80077b1b2500000618bd4000000037400000000178000000000003105000
noncomputable def e84d_target1 : Nat := 0x30000000002201000
noncomputable def e84d_target2 : Nat := 0x300201000
noncomputable def e84d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 153
  maxLength := 5
  maxWidth := 49
  terms := 1
  left := e84d_left
  right := e84d_right
  scale := e84d_scale
  target0 := e84d_target0
  target1 := e84d_target1
  target2 := e84d_target2

theorem e84d_ok : e84d.check=true := by decide +kernel
noncomputable def e85n_left_0 : Nat := 0xffffe6f4d94f5d600845a8760f500403a9d959c3000084528e7580000018b8a1ac000000026d6500000000003fd00000000000003b07000
noncomputable def e85n_left : Nat → Nat
  | 0 => e85n_left_0
  | _ => 0
noncomputable def e85n_right_0 : Nat := 0x300201000
noncomputable def e85n_right : Nat → Nat
  | 0 => e85n_right_0
  | _ => 0
noncomputable def e85n_scale : Nat := 0xf80000000000000004001000
noncomputable def e85n_target0 : Nat := 0x1ffffcde9b29eba800802116a1d83d40000201d4ecace1800000084528e758000000003171435800000000009b5940000000000001fe80000000000000004607000
noncomputable def e85n_target1 : Nat := 0x1f00000000000003501000
noncomputable def e85n_target2 : Nat := 0x300201000
noncomputable def e85n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 218
  maxLength := 7
  maxWidth := 70
  terms := 1
  left := e85n_left
  right := e85n_right
  scale := e85n_scale
  target0 := e85n_target0
  target1 := e85n_target1
  target2 := e85n_target2

theorem e85n_ok : e85n.check=true := by decide +kernel
noncomputable def e85d_left_0 : Nat := 0xfceee18557a7676e00565d380000cf800000150000000002505000
noncomputable def e85d_left : Nat → Nat
  | 0 => e85d_left_0
  | _ => 0
noncomputable def e85d_right_0 : Nat := 0x300201000
noncomputable def e85d_right : Nat → Nat
  | 0 => e85d_right_0
  | _ => 0
noncomputable def e85d_scale : Nat := 0x38000000000002e01000
noncomputable def e85d_target0 : Nat := 0xfb665247f80077b1b2500000618bd4000000037400000000178000000000003105000
noncomputable def e85d_target1 : Nat := 0x30000000002201000
noncomputable def e85d_target2 : Nat := 0x300201000
noncomputable def e85d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 153
  maxLength := 5
  maxWidth := 49
  terms := 1
  left := e85d_left
  right := e85d_right
  scale := e85d_scale
  target0 := e85d_target0
  target1 := e85d_target1
  target2 := e85d_target2

theorem e85d_ok : e85d.check=true := by decide +kernel
noncomputable def e86n_left_0 : Nat := 0x7fffd9bc81f3fe0bd1bffe87484b776285c02001863d449a80e0001021f8d1590fb0000007e5aacabdc80000000434099bd400000000031a61ba00000000000149b90000000000000004908000
noncomputable def e86n_left : Nat → Nat
  | 0 => e86n_left_0
  | _ => 0
noncomputable def e86n_right_0 : Nat := 0x300201000
noncomputable def e86n_right : Nat → Nat
  | 0 => e86n_right_0
  | _ => 0
noncomputable def e86n_scale : Nat := 0x1f0000000000000000004901000
noncomputable def e86n_target0 : Nat := 0x7fffd9bc81f3fe0bd1803ffe87484b776285c0002001863d449a80e000001021f8d1590fb000000007e5aacabdc8000000000434099bd40000000000031a61ba0000000000000149b9000000000000000005108000
noncomputable def e86n_target1 : Nat := 0x1f00000000000000004101000
noncomputable def e86n_target2 : Nat := 0x300201000
noncomputable def e86n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 252
  maxLength := 8
  maxWidth := 81
  terms := 1
  left := e86n_left
  right := e86n_right
  scale := e86n_scale
  target0 := e86n_target0
  target1 := e86n_target1
  target2 := e86n_target2

theorem e86n_ok : e86n.check=true := by decide +kernel
noncomputable def e86d_left_0 : Nat := 0xfceee18557a7676e00565d380000cf800000150000000002505000
noncomputable def e86d_left : Nat → Nat
  | 0 => e86d_left_0
  | _ => 0
noncomputable def e86d_right_0 : Nat := 0x300201000
noncomputable def e86d_right : Nat → Nat
  | 0 => e86d_right_0
  | _ => 0
noncomputable def e86d_scale : Nat := 0x70000000000002f01000
noncomputable def e86d_target0 : Nat := 0x1f6cca48ff00077b1b250000030c5ea00000000dd0000000002f0000000000003205000
noncomputable def e86d_target1 : Nat := 0x30000000002201000
noncomputable def e86d_target2 : Nat := 0x300201000
noncomputable def e86d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 156
  maxLength := 5
  maxWidth := 50
  terms := 1
  left := e86d_left
  right := e86d_right
  scale := e86d_scale
  target0 := e86d_target0
  target1 := e86d_target1
  target2 := e86d_target2

theorem e86d_ok : e86d.check=true := by decide +kernel
noncomputable def e87n_left_0 : Nat := 0x7ffaf53df0358106bfd74776d040de401fe5606437e520000f700f8329500000015d89beb8000000012738ec00000000018566000000000000f70000000000000004108000
noncomputable def e87n_left : Nat → Nat
  | 0 => e87n_left_0
  | _ => 0
noncomputable def e87n_right_0 : Nat := 0x300201000
noncomputable def e87n_right : Nat → Nat
  | 0 => e87n_right_0
  | _ => 0
noncomputable def e87n_scale : Nat := 0xf8000000000000000004801000
noncomputable def e87n_target0 : Nat := 0x7ffaf53df03581068003fd74776d040de400001fe5606437e520000000f700f8329500000000015d89beb8000000000012738ec00000000000018566000000000000000f70000000000000000004d08000
noncomputable def e87n_target1 : Nat := 0xf8000000000000003c01000
noncomputable def e87n_target2 : Nat := 0x300201000
noncomputable def e87n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 240
  maxLength := 8
  maxWidth := 77
  terms := 1
  left := e87n_left
  right := e87n_right
  scale := e87n_scale
  target0 := e87n_target0
  target1 := e87n_target1
  target2 := e87n_target2

theorem e87n_ok : e87n.check=true := by decide +kernel
noncomputable def e87d_left_0 : Nat := 0xfceee18557a7676e00565d380000cf800000150000000002505000
noncomputable def e87d_left : Nat → Nat
  | 0 => e87d_left_0
  | _ => 0
noncomputable def e87d_right_0 : Nat := 0x300201000
noncomputable def e87d_right : Nat → Nat
  | 0 => e87d_right_0
  | _ => 0
noncomputable def e87d_scale : Nat := 0x38000000000002e01000
noncomputable def e87d_target0 : Nat := 0xfb665247f80077b1b2500000618bd4000000037400000000178000000000003105000
noncomputable def e87d_target1 : Nat := 0x30000000002201000
noncomputable def e87d_target2 : Nat := 0x300201000
noncomputable def e87d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 153
  maxLength := 5
  maxWidth := 49
  terms := 1
  left := e87d_left
  right := e87d_right
  scale := e87d_scale
  target0 := e87d_target0
  target1 := e87d_target1
  target2 := e87d_target2

theorem e87d_ok : e87d.check=true := by decide +kernel
noncomputable def e88n_left_0 : Nat := 0x80008f3b016f6b6deff99dd6b944dacc01fec16729d03180004150a6c2027000000335a584ba00000000a0ace2400000000023b8880000000000045d0000000000000004308000
noncomputable def e88n_left : Nat → Nat
  | 0 => e88n_left_0
  | _ => 0
noncomputable def e88n_right_0 : Nat := 0x300201000
noncomputable def e88n_right : Nat → Nat
  | 0 => e88n_right_0
  | _ => 0
noncomputable def e88n_scale : Nat := 0xf8000000000000000004801000
noncomputable def e88n_target0 : Nat := 0x80008f3b016f6b6de001ff33bad7289b59800007fb059ca740c600000020a85361013800000000335a584ba000000000014159c480000000000008ee220000000000000022e8000000000000000004e08000
noncomputable def e88n_target1 : Nat := 0x1f0000000000000003d01000
noncomputable def e88n_target2 : Nat := 0x300201000
noncomputable def e88n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 243
  maxLength := 8
  maxWidth := 78
  terms := 1
  left := e88n_left
  right := e88n_right
  scale := e88n_scale
  target0 := e88n_target0
  target1 := e88n_target1
  target2 := e88n_target2

theorem e88n_ok : e88n.check=true := by decide +kernel
noncomputable def e88d_left_0 : Nat := 0xfceee18557a7676e00565d380000cf800000150000000002505000
noncomputable def e88d_left : Nat → Nat
  | 0 => e88d_left_0
  | _ => 0
noncomputable def e88d_right_0 : Nat := 0x300201000
noncomputable def e88d_right : Nat → Nat
  | 0 => e88d_right_0
  | _ => 0
noncomputable def e88d_scale : Nat := 0x38000000000002e01000
noncomputable def e88d_target0 : Nat := 0xfb665247f80077b1b2500000618bd4000000037400000000178000000000003105000
noncomputable def e88d_target1 : Nat := 0x30000000002201000
noncomputable def e88d_target2 : Nat := 0x300201000
noncomputable def e88d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 153
  maxLength := 5
  maxWidth := 49
  terms := 1
  left := e88d_left
  right := e88d_right
  scale := e88d_scale
  target0 := e88d_target0
  target1 := e88d_target1
  target2 := e88d_target2

theorem e88d_ok : e88d.check=true := by decide +kernel
noncomputable def e89n_left_0 : Nat := 0x809e18a7317cf878ac009f2f360000c1cc000000a10000000002805000
noncomputable def e89n_left : Nat → Nat
  | 0 => e89n_left_0
  | _ => 0
noncomputable def e89n_right_0 : Nat := 0x300201000
noncomputable def e89n_right : Nat → Nat
  | 0 => e89n_right_0
  | _ => 0
noncomputable def e89n_scale : Nat := 0x7000000000002b01000
noncomputable def e89n_target0 : Nat := 0x1013c314e62007cf878ac00004f979b000000307300000000142000000000003105000
noncomputable def e89n_target1 : Nat := 0x38000000002201000
noncomputable def e89n_target2 : Nat := 0x300201000
noncomputable def e89n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 153
  maxLength := 5
  maxWidth := 49
  terms := 1
  left := e89n_left
  right := e89n_right
  scale := e89n_scale
  target0 := e89n_target0
  target1 := e89n_target1
  target2 := e89n_target2

theorem e89n_ok : e89n.check=true := by decide +kernel
noncomputable def e89d_left_0 : Nat := 0x54f0000a02000
noncomputable def e89d_left : Nat → Nat
  | 0 => e89d_left_0
  | _ => 0
noncomputable def e89d_right_0 : Nat := 0x300201000
noncomputable def e89d_right : Nat → Nat
  | 0 => e89d_right_0
  | _ => 0
noncomputable def e89d_scale : Nat := 0x7000001301000
noncomputable def e89d_target0 : Nat := 0xfc807000001302000
noncomputable def e89d_target1 : Nat := 0x30000a01000
noncomputable def e89d_target2 : Nat := 0x300201000
noncomputable def e89d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 60
  maxLength := 2
  maxWidth := 19
  terms := 1
  left := e89d_left
  right := e89d_right
  scale := e89d_scale
  target0 := e89d_target0
  target1 := e89d_target1
  target2 := e89d_target2

theorem e89d_ok : e89d.check=true := by decide +kernel
end ThomsonNegative.Certificate.Bridges.RFChecks
