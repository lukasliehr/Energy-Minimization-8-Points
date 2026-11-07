import ThomsonNegative.Structure.Packed.IdentityKernel
namespace ThomsonNegative.Certificate.Bridges.RFChecks
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
noncomputable def e100n_left_0 : Nat := 0x7eda1536b5b72c02f5480007100000001f04000
noncomputable def e100n_left : Nat → Nat
  | 0 => e100n_left_0
  | _ => 0
noncomputable def e100n_right_0 : Nat := 0x300201000
noncomputable def e100n_right : Nat → Nat
  | 0 => e100n_right_0
  | _ => 0
noncomputable def e100n_scale : Nat := 0x70000000002301000
noncomputable def e100n_target0 : Nat := 0x7eda153600b5b72c0002f54800000710000000002704000
noncomputable def e100n_target1 : Nat := 0x700000001b01000
noncomputable def e100n_target2 : Nat := 0x300201000
noncomputable def e100n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 123
  maxLength := 4
  maxWidth := 39
  terms := 1
  left := e100n_left
  right := e100n_right
  scale := e100n_scale
  target0 := e100n_target0
  target1 := e100n_target1
  target2 := e100n_target2

theorem e100n_ok : e100n.check=true := by decide +kernel
noncomputable def e100d_left_0 : Nat := 0x54f0000a02000
noncomputable def e100d_left : Nat → Nat
  | 0 => e100d_left_0
  | _ => 0
noncomputable def e100d_right_0 : Nat := 0x300201000
noncomputable def e100d_right : Nat → Nat
  | 0 => e100d_right_0
  | _ => 0
noncomputable def e100d_scale : Nat := 0x7000001301000
noncomputable def e100d_target0 : Nat := 0xfc807000001302000
noncomputable def e100d_target1 : Nat := 0x30000a01000
noncomputable def e100d_target2 : Nat := 0x300201000
noncomputable def e100d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 60
  maxLength := 2
  maxWidth := 19
  terms := 1
  left := e100d_left
  right := e100d_right
  scale := e100d_scale
  target0 := e100d_target0
  target1 := e100d_target1
  target2 := e100d_target2

theorem e100d_ok : e100d.check=true := by decide +kernel
noncomputable def e101n_left_0 : Nat := 0x8005e65c1392f4b80948e075e676008581d625b9d000092209f0140000007bf09150000000014b16000000000026300000000000003c07000
noncomputable def e101n_left : Nat → Nat
  | 0 => e101n_left_0
  | _ => 0
noncomputable def e101n_right_0 : Nat := 0x300201000
noncomputable def e101n_right : Nat → Nat
  | 0 => e101n_right_0
  | _ => 0
noncomputable def e101n_scale : Nat := 0x3680000000000000004201000
noncomputable def e101n_target0 : Nat := 0x4002f32e09c97a58020252381d799d800010b03ac4b73a00000092209f014000000003df848a8000000000052c580000000000004c60000000000000004507000
noncomputable def e101n_target1 : Nat := 0x1b400000000000003901000
noncomputable def e101n_target2 : Nat := 0x300201000
noncomputable def e101n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 215
  maxLength := 7
  maxWidth := 69
  terms := 1
  left := e101n_left
  right := e101n_right
  scale := e101n_scale
  target0 := e101n_target0
  target1 := e101n_target1
  target2 := e101n_target2

theorem e101n_ok : e101n.check=true := by decide +kernel
noncomputable def e101d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e101d_left : Nat → Nat
  | 0 => e101d_left_0
  | _ => 0
noncomputable def e101d_right_0 : Nat := 0x300201000
noncomputable def e101d_right : Nat → Nat
  | 0 => e101d_right_0
  | _ => 0
noncomputable def e101d_scale : Nat := 0xc800000000000003801000
noncomputable def e101d_target0 : Nat := 0x1fdc34304001c003e20aa3b78800008a15c65600000012d1b24000000000e3cc000000000056800000000000003b06000
noncomputable def e101d_target1 : Nat := 0x3000000000002a01000
noncomputable def e101d_target2 : Nat := 0x300201000
noncomputable def e101d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 184
  maxLength := 6
  maxWidth := 59
  terms := 1
  left := e101d_left
  right := e101d_right
  scale := e101d_scale
  target0 := e101d_target0
  target1 := e101d_target1
  target2 := e101d_target2

theorem e101d_ok : e101d.check=true := by decide +kernel
noncomputable def e102n_left_0 : Nat := 0x7ffe481f96268569aff6ebe8bb1f586401f1f01d0fb014800037e84b57c7500000074e8f1c2e00000001a6ab26c0000000003d3198000000000005170000000000000004308000
noncomputable def e102n_left : Nat → Nat
  | 0 => e102n_left_0
  | _ => 0
noncomputable def e102n_right_0 : Nat := 0x300201000
noncomputable def e102n_right : Nat → Nat
  | 0 => e102n_right_0
  | _ => 0
noncomputable def e102n_scale : Nat := 0x368000000000000000004a01000
noncomputable def e102n_target0 : Nat := 0x7ffe481f96268569a003fdbafa2ec7d61900001f1f01d0fb0148000000dfa12d5f1d40000000074e8f1c2e000000000069aac9b0000000000003d31980000000000000145c000000000000000004d08000
noncomputable def e102n_target1 : Nat := 0xda0000000000000004001000
noncomputable def e102n_target2 : Nat := 0x300201000
noncomputable def e102n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 240
  maxLength := 8
  maxWidth := 77
  terms := 1
  left := e102n_left
  right := e102n_right
  scale := e102n_scale
  target0 := e102n_target0
  target1 := e102n_target1
  target2 := e102n_target2

theorem e102n_ok : e102n.check=true := by decide +kernel
noncomputable def e102d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e102d_left : Nat → Nat
  | 0 => e102d_left_0
  | _ => 0
noncomputable def e102d_right_0 : Nat := 0x300201000
noncomputable def e102d_right : Nat → Nat
  | 0 => e102d_right_0
  | _ => 0
noncomputable def e102d_scale : Nat := 0xc800000000000003801000
noncomputable def e102d_target0 : Nat := 0x1fdc34304001c003e20aa3b78800008a15c65600000012d1b24000000000e3cc000000000056800000000000003b06000
noncomputable def e102d_target1 : Nat := 0x3000000000002a01000
noncomputable def e102d_target2 : Nat := 0x300201000
noncomputable def e102d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 184
  maxLength := 6
  maxWidth := 59
  terms := 1
  left := e102d_left
  right := e102d_right
  scale := e102d_scale
  target0 := e102d_target0
  target1 := e102d_target1
  target2 := e102d_target2

theorem e102d_ok : e102d.check=true := by decide +kernel
noncomputable def e103n_left_0 : Nat := 0x7fff15e5b80fcdf617fd6550aa3e115d007da94a2b0912d000074eac7d60a90000007e9118f1300000000c1497a70000000000ab71f0000000000007930000000000000004408000
noncomputable def e103n_left : Nat → Nat
  | 0 => e103n_left_0
  | _ => 0
noncomputable def e103n_right_0 : Nat := 0x300201000
noncomputable def e103n_right : Nat → Nat
  | 0 => e103n_right_0
  | _ => 0
noncomputable def e103n_scale : Nat := 0x368000000000000000004a01000
noncomputable def e103n_target0 : Nat := 0x7fff15e5b80fcdf61001ff59542a8f8457400007da94a2b0912d0000001d3ab1f582a4000000007e9118f13000000000030525e9c000000000000ab71f000000000000001e4c000000000000000004e08000
noncomputable def e103n_target1 : Nat := 0xda0000000000000004001000
noncomputable def e103n_target2 : Nat := 0x300201000
noncomputable def e103n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 243
  maxLength := 8
  maxWidth := 78
  terms := 1
  left := e103n_left
  right := e103n_right
  scale := e103n_scale
  target0 := e103n_target0
  target1 := e103n_target1
  target2 := e103n_target2

theorem e103n_ok : e103n.check=true := by decide +kernel
noncomputable def e103d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e103d_left : Nat → Nat
  | 0 => e103d_left_0
  | _ => 0
noncomputable def e103d_right_0 : Nat := 0x300201000
noncomputable def e103d_right : Nat → Nat
  | 0 => e103d_right_0
  | _ => 0
noncomputable def e103d_scale : Nat := 0xc800000000000003801000
noncomputable def e103d_target0 : Nat := 0x1fdc34304001c003e20aa3b78800008a15c65600000012d1b24000000000e3cc000000000056800000000000003b06000
noncomputable def e103d_target1 : Nat := 0x3000000000002a01000
noncomputable def e103d_target2 : Nat := 0x300201000
noncomputable def e103d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 184
  maxLength := 6
  maxWidth := 59
  terms := 1
  left := e103d_left
  right := e103d_right
  scale := e103d_scale
  target0 := e103d_target0
  target1 := e103d_target1
  target2 := e103d_target2

theorem e103d_ok : e103d.check=true := by decide +kernel
noncomputable def e104n_left_0 : Nat := 0x857aab16c81950011dc0000f00000001e04000
noncomputable def e104n_left : Nat → Nat
  | 0 => e104n_left_0
  | _ => 0
noncomputable def e104n_right_0 : Nat := 0x300201000
noncomputable def e104n_right : Nat → Nat
  | 0 => e104n_right_0
  | _ => 0
noncomputable def e104n_scale : Nat := 0x190000000002501000
noncomputable def e104n_target0 : Nat := 0x857aab1402c8195000011dc000000f0000000002604000
noncomputable def e104n_target1 : Nat := 0x1900000001d01000
noncomputable def e104n_target2 : Nat := 0x300201000
noncomputable def e104n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 120
  maxLength := 4
  maxWidth := 38
  terms := 1
  left := e104n_left
  right := e104n_right
  scale := e104n_scale
  target0 := e104n_target0
  target1 := e104n_target1
  target2 := e104n_target2

theorem e104n_ok : e104n.check=true := by decide +kernel
noncomputable def e104d_left_0 : Nat := 0x54f0000a02000
noncomputable def e104d_left : Nat → Nat
  | 0 => e104d_left_0
  | _ => 0
noncomputable def e104d_right_0 : Nat := 0x300201000
noncomputable def e104d_right : Nat → Nat
  | 0 => e104d_right_0
  | _ => 0
noncomputable def e104d_scale : Nat := 0x19000001501000
noncomputable def e104d_target0 : Nat := 0x13d6019000001502000
noncomputable def e104d_target1 : Nat := 0x30000a01000
noncomputable def e104d_target2 : Nat := 0x300201000
noncomputable def e104d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 66
  maxLength := 2
  maxWidth := 21
  terms := 1
  left := e104d_left
  right := e104d_right
  scale := e104d_scale
  target0 := e104d_target0
  target1 := e104d_target1
  target2 := e104d_target2

theorem e104d_ok : e104d.check=true := by decide +kernel
noncomputable def e105n_left_0 : Nat := 0x200cb656f0f84f933d50028aaf4a0000e00d00000031f0000000002a05000
noncomputable def e105n_left : Nat → Nat
  | 0 => e105n_left_0
  | _ => 0
noncomputable def e105n_right_0 : Nat := 0x300201000
noncomputable def e105n_right : Nat → Nat
  | 0 => e105n_right_0
  | _ => 0
noncomputable def e105n_scale : Nat := 0xf8000000000003001000
noncomputable def e105n_target0 : Nat := 0x200cb656f0f0084f933d5000028aaf4a000000e00d0000000031f000000000003205000
noncomputable def e105n_target1 : Nat := 0xf80000000002801000
noncomputable def e105n_target2 : Nat := 0x300201000
noncomputable def e105n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 156
  maxLength := 5
  maxWidth := 50
  terms := 1
  left := e105n_left
  right := e105n_right
  scale := e105n_scale
  target0 := e105n_target0
  target1 := e105n_target1
  target2 := e105n_target2

theorem e105n_ok : e105n.check=true := by decide +kernel
noncomputable def e105d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e105d_left : Nat → Nat
  | 0 => e105d_left_0
  | _ => 0
noncomputable def e105d_right_0 : Nat := 0x300201000
noncomputable def e105d_right : Nat → Nat
  | 0 => e105d_right_0
  | _ => 0
noncomputable def e105d_scale : Nat := 0x3800000000000003601000
noncomputable def e105d_target0 : Nat := 0x1fd04595aaad000f6038be7d800008d725dc80000004f090c000000000851000000000017800000000000003906000
noncomputable def e105d_target1 : Nat := 0x3000000000002a01000
noncomputable def e105d_target2 : Nat := 0x300201000
noncomputable def e105d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 178
  maxLength := 6
  maxWidth := 57
  terms := 1
  left := e105d_left
  right := e105d_right
  scale := e105d_scale
  target0 := e105d_target0
  target1 := e105d_target1
  target2 := e105d_target2

theorem e105d_ok : e105d.check=true := by decide +kernel
noncomputable def e106n_left_0 : Nat := 0x1ffc18a9f9cdafbc4b8cdbb0068740f79000012ad0180000007a2200000000cf000000000003106000
noncomputable def e106n_left : Nat → Nat
  | 0 => e106n_left_0
  | _ => 0
noncomputable def e106n_right_0 : Nat := 0x300201000
noncomputable def e106n_right : Nat → Nat
  | 0 => e106n_right_0
  | _ => 0
noncomputable def e106n_scale : Nat := 0xf800000000000003801000
noncomputable def e106n_target0 : Nat := 0x7ff062a7e736801f789719b76000068740f79000000095680c000000001e88800000000019e00000000000003a06000
noncomputable def e106n_target1 : Nat := 0x7c000000000002f01000
noncomputable def e106n_target2 : Nat := 0x300201000
noncomputable def e106n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 181
  maxLength := 6
  maxWidth := 58
  terms := 1
  left := e106n_left
  right := e106n_right
  scale := e106n_scale
  target0 := e106n_target0
  target1 := e106n_target1
  target2 := e106n_target2

theorem e106n_ok : e106n.check=true := by decide +kernel
noncomputable def e106d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e106d_left : Nat → Nat
  | 0 => e106d_left_0
  | _ => 0
noncomputable def e106d_right_0 : Nat := 0x300201000
noncomputable def e106d_right : Nat → Nat
  | 0 => e106d_right_0
  | _ => 0
noncomputable def e106d_scale : Nat := 0x3800000000000003601000
noncomputable def e106d_target0 : Nat := 0x1fd04595aaad000f6038be7d800008d725dc80000004f090c000000000851000000000017800000000000003906000
noncomputable def e106d_target1 : Nat := 0x3000000000002a01000
noncomputable def e106d_target2 : Nat := 0x300201000
noncomputable def e106d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 178
  maxLength := 6
  maxWidth := 57
  terms := 1
  left := e106d_left
  right := e106d_right
  scale := e106d_scale
  target0 := e106d_target0
  target1 := e106d_target1
  target2 := e106d_target2

theorem e106d_ok : e106d.check=true := by decide +kernel
noncomputable def e107n_left_0 : Nat := 0x7ffb88f497b77cd5834201005bd9a736000014bbb20000004763000000007d000000000003006000
noncomputable def e107n_left : Nat → Nat
  | 0 => e107n_left_0
  | _ => 0
noncomputable def e107n_right_0 : Nat := 0x300201000
noncomputable def e107n_right : Nat → Nat
  | 0 => e107n_right_0
  | _ => 0
noncomputable def e107n_scale : Nat := 0xf800000000000003801000
noncomputable def e107n_target0 : Nat := 0x7ffb88f497b7001f3560d080400005bd9a736000000052eec800000000476300000000001f400000000000003a06000
noncomputable def e107n_target1 : Nat := 0x3e000000000002e01000
noncomputable def e107n_target2 : Nat := 0x300201000
noncomputable def e107n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 181
  maxLength := 6
  maxWidth := 58
  terms := 1
  left := e107n_left
  right := e107n_right
  scale := e107n_scale
  target0 := e107n_target0
  target1 := e107n_target1
  target2 := e107n_target2

theorem e107n_ok : e107n.check=true := by decide +kernel
noncomputable def e107d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e107d_left : Nat → Nat
  | 0 => e107d_left_0
  | _ => 0
noncomputable def e107d_right_0 : Nat := 0x300201000
noncomputable def e107d_right : Nat → Nat
  | 0 => e107d_right_0
  | _ => 0
noncomputable def e107d_scale : Nat := 0x3800000000000003601000
noncomputable def e107d_target0 : Nat := 0x1fd04595aaad000f6038be7d800008d725dc80000004f090c000000000851000000000017800000000000003906000
noncomputable def e107d_target1 : Nat := 0x3000000000002a01000
noncomputable def e107d_target2 : Nat := 0x300201000
noncomputable def e107d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 178
  maxLength := 6
  maxWidth := 57
  terms := 1
  left := e107d_left
  right := e107d_right
  scale := e107d_scale
  target0 := e107d_target0
  target1 := e107d_target1
  target2 := e107d_target2

theorem e107d_ok : e107d.check=true := by decide +kernel
noncomputable def e108n_left_0 : Nat := 0x3ffecaca5dba4395ff57194f19ed400ff411c06b3300007c09e0b160000002debb6ec000000005159400000000005cd00000000000003d07000
noncomputable def e108n_left : Nat → Nat
  | 0 => e108n_left_0
  | _ => 0
noncomputable def e108n_right_0 : Nat := 0x300201000
noncomputable def e108n_right : Nat → Nat
  | 0 => e108n_right_0
  | _ => 0
noncomputable def e108n_scale : Nat := 0x1f00000000000000004101000
noncomputable def e108n_target0 : Nat := 0x3ffecaca5dba439401ff57194f19ed40000ff411c06b330000007c09e0b16000000002debb6ec0000000000515940000000000005cd0000000000000004507000
noncomputable def e108n_target1 : Nat := 0x1f000000000000003901000
noncomputable def e108n_target2 : Nat := 0x300201000
noncomputable def e108n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 215
  maxLength := 7
  maxWidth := 69
  terms := 1
  left := e108n_left
  right := e108n_right
  scale := e108n_scale
  target0 := e108n_target0
  target1 := e108n_target1
  target2 := e108n_target2

theorem e108n_ok : e108n.check=true := by decide +kernel
noncomputable def e108d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e108d_left : Nat → Nat
  | 0 => e108d_left_0
  | _ => 0
noncomputable def e108d_right_0 : Nat := 0x300201000
noncomputable def e108d_right : Nat → Nat
  | 0 => e108d_right_0
  | _ => 0
noncomputable def e108d_scale : Nat := 0x7000000000000003701000
noncomputable def e108d_target0 : Nat := 0x7f411656aab4001ec0717cfb000008d725dc8000000278486000000000214400000000002f000000000000003a06000
noncomputable def e108d_target1 : Nat := 0x3000000000002a01000
noncomputable def e108d_target2 : Nat := 0x300201000
noncomputable def e108d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 181
  maxLength := 6
  maxWidth := 58
  terms := 1
  left := e108d_left
  right := e108d_right
  scale := e108d_scale
  target0 := e108d_target0
  target1 := e108d_target1
  target2 := e108d_target2

theorem e108d_ok : e108d.check=true := by decide +kernel
noncomputable def e109n_left_0 : Nat := 0x801ea73826711582e20b45f34a0098dfee14030000d588886c000000db288b00000000a6aa00000000007d00000000000003807000
noncomputable def e109n_left : Nat → Nat
  | 0 => e109n_left_0
  | _ => 0
noncomputable def e109n_right_0 : Nat := 0x300201000
noncomputable def e109n_right : Nat → Nat
  | 0 => e109n_right_0
  | _ => 0
noncomputable def e109n_scale : Nat := 0xf80000000000000004001000
noncomputable def e109n_target0 : Nat := 0x2007a9ce099c4540082e20b45f34a00002637fb8500c000000d588886c0000000036ca22c0000000000a6aa0000000000001f40000000000000004207000
noncomputable def e109n_target1 : Nat := 0x3e00000000000003601000
noncomputable def e109n_target2 : Nat := 0x300201000
noncomputable def e109n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 206
  maxLength := 7
  maxWidth := 66
  terms := 1
  left := e109n_left
  right := e109n_right
  scale := e109n_scale
  target0 := e109n_target0
  target1 := e109n_target1
  target2 := e109n_target2

theorem e109n_ok : e109n.check=true := by decide +kernel
noncomputable def e109d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e109d_left : Nat → Nat
  | 0 => e109d_left_0
  | _ => 0
noncomputable def e109d_right_0 : Nat := 0x300201000
noncomputable def e109d_right : Nat → Nat
  | 0 => e109d_right_0
  | _ => 0
noncomputable def e109d_scale : Nat := 0x3800000000000003601000
noncomputable def e109d_target0 : Nat := 0x1fd04595aaad000f6038be7d800008d725dc80000004f090c000000000851000000000017800000000000003906000
noncomputable def e109d_target1 : Nat := 0x3000000000002a01000
noncomputable def e109d_target2 : Nat := 0x300201000
noncomputable def e109d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 178
  maxLength := 6
  maxWidth := 57
  terms := 1
  left := e109d_left
  right := e109d_right
  scale := e109d_scale
  target0 := e109d_target0
  target1 := e109d_target1
  target2 := e109d_target2

theorem e109d_ok : e109d.check=true := by decide +kernel
end ThomsonNegative.Certificate.Bridges.RFChecks
