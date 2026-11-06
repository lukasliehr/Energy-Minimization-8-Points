import ThomsonNegative.Structure.Packed.IdentityKernel
namespace ThomsonNegative.Certificate.Bridges.RFChecks
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
noncomputable def e130n_left_0 : Nat := 0x80008978f300adbd9efff1f738824bae4c01ff1835923912180003ffe589a4f870000007d2f09f4fa00000000b847f0a40000000000c10d88000000000002b7d0000000000000004708000
noncomputable def e130n_left : Nat → Nat
  | 0 => e130n_left_0
  | _ => 0
noncomputable def e130n_right_0 : Nat := 0x300201000
noncomputable def e130n_right : Nat → Nat
  | 0 => e130n_right_0
  | _ => 0
noncomputable def e130n_scale : Nat := 0x68000000000000000004701000
noncomputable def e130n_target0 : Nat := 0x80008978f300adbd9e00fff1f738824bae4c0001ff183592391218000003ffe589a4f87000000007d2f09f4fa0000000000b847f0a4000000000000c10d8800000000000002b7d000000000000000004f08000
noncomputable def e130n_target1 : Nat := 0x680000000000000003f01000
noncomputable def e130n_target2 : Nat := 0x300201000
noncomputable def e130n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 246
  maxLength := 8
  maxWidth := 79
  terms := 1
  left := e130n_left
  right := e130n_right
  scale := e130n_scale
  target0 := e130n_target0
  target1 := e130n_target1
  target2 := e130n_target2

theorem e130n_ok : e130n.check=true := by decide +kernel
noncomputable def e130d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e130d_left : Nat → Nat
  | 0 => e130d_left_0
  | _ => 0
noncomputable def e130d_right_0 : Nat := 0x300201000
noncomputable def e130d_right : Nat → Nat
  | 0 => e130d_right_0
  | _ => 0
noncomputable def e130d_scale : Nat := 0x1800000000000003501000
noncomputable def e130d_target0 : Nat := 0x1fc05cc78e3c003cabd94d48000091edd2600000015030400000000006c00000000006800000000000003706000
noncomputable def e130d_target1 : Nat := 0x3000000000002a01000
noncomputable def e130d_target2 : Nat := 0x300201000
noncomputable def e130d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 172
  maxLength := 6
  maxWidth := 55
  terms := 1
  left := e130d_left
  right := e130d_right
  scale := e130d_scale
  target0 := e130d_target0
  target1 := e130d_target1
  target2 := e130d_target2

theorem e130d_ok : e130d.check=true := by decide +kernel
noncomputable def e131n_left_0 : Nat := 0x7ffeb27959233b517fef7cb8ccec2d00820d9109599d00009944b99479000000c316f16300000000b5a8970000000000906f000000000000830000000000000004008000
noncomputable def e131n_left : Nat → Nat
  | 0 => e131n_left_0
  | _ => 0
noncomputable def e131n_right_0 : Nat := 0x300201000
noncomputable def e131n_right : Nat → Nat
  | 0 => e131n_right_0
  | _ => 0
noncomputable def e131n_scale : Nat := 0x34000000000000000004601000
noncomputable def e131n_target0 : Nat := 0x7ffeb27959233b510007fef7cb8ccec2d00000820d9109599d00000009944b99479000000000c316f16300000000000b5a8970000000000000906f000000000000000830000000000000000004c08000
noncomputable def e131n_target1 : Nat := 0x34000000000000003a01000
noncomputable def e131n_target2 : Nat := 0x300201000
noncomputable def e131n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 237
  maxLength := 8
  maxWidth := 76
  terms := 1
  left := e131n_left
  right := e131n_right
  scale := e131n_scale
  target0 := e131n_target0
  target1 := e131n_target1
  target2 := e131n_target2

theorem e131n_ok : e131n.check=true := by decide +kernel
noncomputable def e131d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e131d_left : Nat → Nat
  | 0 => e131d_left_0
  | _ => 0
noncomputable def e131d_right_0 : Nat := 0x300201000
noncomputable def e131d_right : Nat → Nat
  | 0 => e131d_right_0
  | _ => 0
noncomputable def e131d_scale : Nat := 0xc00000000000003401000
noncomputable def e131d_target0 : Nat := 0x7f01731e38f001e55eca6a4000091edd260000002a06080000000001b00000000003400000000000003606000
noncomputable def e131d_target1 : Nat := 0x3000000000002a01000
noncomputable def e131d_target2 : Nat := 0x300201000
noncomputable def e131d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 169
  maxLength := 6
  maxWidth := 54
  terms := 1
  left := e131d_left
  right := e131d_right
  scale := e131d_scale
  target0 := e131d_target0
  target1 := e131d_target1
  target2 := e131d_target2

theorem e131d_ok : e131d.check=true := by decide +kernel
noncomputable def e132n_left_0 : Nat := 0x7fffc50123ee18a3dff8793e703bd53008173c7cab740c000273691b3c47000000d4f0356f400000002d7796900000000006dfc4000000000001bd0000000000000004208000
noncomputable def e132n_left : Nat → Nat
  | 0 => e132n_left_0
  | _ => 0
noncomputable def e132n_right_0 : Nat := 0x300201000
noncomputable def e132n_right : Nat → Nat
  | 0 => e132n_right_0
  | _ => 0
noncomputable def e132n_scale : Nat := 0x34000000000000000004601000
noncomputable def e132n_target0 : Nat := 0x7fffc50123ee18a3c007fe1e4f9c0ef54c00008173c7cab740c0000009cda46cf11c00000000d4f0356f40000000000b5de5a40000000000006dfc4000000000000006f4000000000000000004c08000
noncomputable def e132n_target1 : Nat := 0xd0000000000000003c01000
noncomputable def e132n_target2 : Nat := 0x300201000
noncomputable def e132n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 237
  maxLength := 8
  maxWidth := 76
  terms := 1
  left := e132n_left
  right := e132n_right
  scale := e132n_scale
  target0 := e132n_target0
  target1 := e132n_target1
  target2 := e132n_target2

theorem e132n_ok : e132n.check=true := by decide +kernel
noncomputable def e132d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e132d_left : Nat → Nat
  | 0 => e132d_left_0
  | _ => 0
noncomputable def e132d_right_0 : Nat := 0x300201000
noncomputable def e132d_right : Nat → Nat
  | 0 => e132d_right_0
  | _ => 0
noncomputable def e132d_scale : Nat := 0xc00000000000003401000
noncomputable def e132d_target0 : Nat := 0x7f01731e38f001e55eca6a4000091edd260000002a06080000000001b00000000003400000000000003606000
noncomputable def e132d_target1 : Nat := 0x3000000000002a01000
noncomputable def e132d_target2 : Nat := 0x300201000
noncomputable def e132d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 169
  maxLength := 6
  maxWidth := 54
  terms := 1
  left := e132d_left
  right := e132d_right
  scale := e132d_scale
  target0 := e132d_target0
  target1 := e132d_target1
  target2 := e132d_target2

theorem e132d_ok : e132d.check=true := by decide +kernel
noncomputable def e133n_left_0 : Nat := 0x8165b706d2e4cc00c5080002900000001f04000
noncomputable def e133n_left : Nat → Nat
  | 0 => e133n_left_0
  | _ => 0
noncomputable def e133n_right_0 : Nat := 0x300201000
noncomputable def e133n_right : Nat → Nat
  | 0 => e133n_right_0
  | _ => 0
noncomputable def e133n_scale : Nat := 0x30000000002201000
noncomputable def e133n_target0 : Nat := 0x8165b7060069726600003142000000520000000002804000
noncomputable def e133n_target1 : Nat := 0x180000001901000
noncomputable def e133n_target2 : Nat := 0x300201000
noncomputable def e133n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 126
  maxLength := 4
  maxWidth := 40
  terms := 1
  left := e133n_left
  right := e133n_right
  scale := e133n_scale
  target0 := e133n_target0
  target1 := e133n_target1
  target2 := e133n_target2

theorem e133n_ok : e133n.check=true := by decide +kernel
noncomputable def e133d_left_0 : Nat := 0x54f0000a02000
noncomputable def e133d_left : Nat → Nat
  | 0 => e133d_left_0
  | _ => 0
noncomputable def e133d_right_0 : Nat := 0x300201000
noncomputable def e133d_right : Nat → Nat
  | 0 => e133d_right_0
  | _ => 0
noncomputable def e133d_scale : Nat := 0x3000001201000
noncomputable def e133d_target0 : Nat := 0x54c03000001202000
noncomputable def e133d_target1 : Nat := 0x30000a01000
noncomputable def e133d_target2 : Nat := 0x300201000
noncomputable def e133d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 57
  maxLength := 2
  maxWidth := 18
  terms := 1
  left := e133d_left
  right := e133d_right
  scale := e133d_scale
  target0 := e133d_target0
  target1 := e133d_target1
  target2 := e133d_target2

theorem e133d_ok : e133d.check=true := by decide +kernel
noncomputable def e134n_left_0 : Nat := 0x3ffffb388d77c49dfffc96887085c0103e11ed7b6100009355b23520000005f3796e40000000309e9c000000000139f00000000000003d07000
noncomputable def e134n_left : Nat → Nat
  | 0 => e134n_left_0
  | _ => 0
noncomputable def e134n_right_0 : Nat := 0x300201000
noncomputable def e134n_right : Nat → Nat
  | 0 => e134n_right_0
  | _ => 0
noncomputable def e134n_scale : Nat := 0x7c0000000000000003f01000
noncomputable def e134n_target0 : Nat := 0x3ffffb388d77c49c01fffc96887085c000103e11ed7b610000009355b2352000000005f3796e4000000000309e9c00000000000139f0000000000000004507000
noncomputable def e134n_target1 : Nat := 0x7c00000000000003701000
noncomputable def e134n_target2 : Nat := 0x300201000
noncomputable def e134n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 215
  maxLength := 7
  maxWidth := 69
  terms := 1
  left := e134n_left
  right := e134n_right
  scale := e134n_scale
  target0 := e134n_target0
  target1 := e134n_target1
  target2 := e134n_target2

theorem e134n_ok : e134n.check=true := by decide +kernel
noncomputable def e134d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e134d_left : Nat → Nat
  | 0 => e134d_left_0
  | _ => 0
noncomputable def e134d_right_0 : Nat := 0x300201000
noncomputable def e134d_right : Nat → Nat
  | 0 => e134d_right_0
  | _ => 0
noncomputable def e134d_scale : Nat := 0x1c00000000000003501000
noncomputable def e134d_target0 : Nat := 0x7f411656aab4007b01c5f3ec00008d725dc80000009e12180000000021440000000000bc00000000000003806000
noncomputable def e134d_target1 : Nat := 0x3000000000002a01000
noncomputable def e134d_target2 : Nat := 0x300201000
noncomputable def e134d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 175
  maxLength := 6
  maxWidth := 56
  terms := 1
  left := e134d_left
  right := e134d_right
  scale := e134d_scale
  target0 := e134d_target0
  target1 := e134d_target1
  target2 := e134d_target2

theorem e134d_ok : e134d.check=true := by decide +kernel
noncomputable def e135n_left_0 : Nat := 0x8000a6fdd48d184f1800784b570b48ad007f40a848f8d7d0000730ac7146b9000000493b1d6c3000000003416e9700000000004d98f0000000000007430000000000000004408000
noncomputable def e135n_left : Nat → Nat
  | 0 => e135n_left_0
  | _ => 0
noncomputable def e135n_right_0 : Nat := 0x300201000
noncomputable def e135n_right : Nat → Nat
  | 0 => e135n_right_0
  | _ => 0
noncomputable def e135n_scale : Nat := 0x7c000000000000000004701000
noncomputable def e135n_target0 : Nat := 0x8000a6fdd48d184f1004003c25ab85a45680001fd02a123e35f4000000e6158e28d7200000000493b1d6c300000000001a0b74b80000000000013663c00000000000000e86000000000000000004d08000
noncomputable def e135n_target1 : Nat := 0x3e0000000000000003e01000
noncomputable def e135n_target2 : Nat := 0x300201000
noncomputable def e135n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 240
  maxLength := 8
  maxWidth := 77
  terms := 1
  left := e135n_left
  right := e135n_right
  scale := e135n_scale
  target0 := e135n_target0
  target1 := e135n_target1
  target2 := e135n_target2

theorem e135n_ok : e135n.check=true := by decide +kernel
noncomputable def e135d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e135d_left : Nat → Nat
  | 0 => e135d_left_0
  | _ => 0
noncomputable def e135d_right_0 : Nat := 0x300201000
noncomputable def e135d_right : Nat → Nat
  | 0 => e135d_right_0
  | _ => 0
noncomputable def e135d_scale : Nat := 0x1c00000000000003501000
noncomputable def e135d_target0 : Nat := 0x7f411656aab4007b01c5f3ec00008d725dc80000009e12180000000021440000000000bc00000000000003806000
noncomputable def e135d_target1 : Nat := 0x3000000000002a01000
noncomputable def e135d_target2 : Nat := 0x300201000
noncomputable def e135d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 175
  maxLength := 6
  maxWidth := 56
  terms := 1
  left := e135d_left
  right := e135d_right
  scale := e135d_scale
  target0 := e135d_target0
  target1 := e135d_target1
  target2 := e135d_target2

theorem e135d_ok : e135d.check=true := by decide +kernel
noncomputable def e136n_left_0 : Nat := 0x7fff9faa3c86fbd9f8011cab207f08a3007f3bf5a81e9d300006da56386b570000003b2d0f3ed000000003c5e259000000000064de100000000000086d0000000000000004408000
noncomputable def e136n_left : Nat → Nat
  | 0 => e136n_left_0
  | _ => 0
noncomputable def e136n_right_0 : Nat := 0x300201000
noncomputable def e136n_right : Nat → Nat
  | 0 => e136n_right_0
  | _ => 0
noncomputable def e136n_scale : Nat := 0x7c000000000000000004701000
noncomputable def e136n_target0 : Nat := 0x7fff9faa3c86fbd9f004008e55903f845180001fcefd6a07a74c000000db4ac70d6ae000000003b2d0f3ed00000000001e2f12c800000000000193784000000000000010da000000000000000004d08000
noncomputable def e136n_target1 : Nat := 0x3e0000000000000003e01000
noncomputable def e136n_target2 : Nat := 0x300201000
noncomputable def e136n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 240
  maxLength := 8
  maxWidth := 77
  terms := 1
  left := e136n_left
  right := e136n_right
  scale := e136n_scale
  target0 := e136n_target0
  target1 := e136n_target1
  target2 := e136n_target2

theorem e136n_ok : e136n.check=true := by decide +kernel
noncomputable def e136d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e136d_left : Nat → Nat
  | 0 => e136d_left_0
  | _ => 0
noncomputable def e136d_right_0 : Nat := 0x300201000
noncomputable def e136d_right : Nat → Nat
  | 0 => e136d_right_0
  | _ => 0
noncomputable def e136d_scale : Nat := 0x1c00000000000003501000
noncomputable def e136d_target0 : Nat := 0x7f411656aab4007b01c5f3ec00008d725dc80000009e12180000000021440000000000bc00000000000003806000
noncomputable def e136d_target1 : Nat := 0x3000000000002a01000
noncomputable def e136d_target2 : Nat := 0x300201000
noncomputable def e136d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 175
  maxLength := 6
  maxWidth := 56
  terms := 1
  left := e136d_left
  right := e136d_right
  scale := e136d_scale
  target0 := e136d_target0
  target1 := e136d_target1
  target2 := e136d_target2

theorem e136d_ok : e136d.check=true := by decide +kernel
noncomputable def e137n_left_0 : Nat := 0x7ee1cff3518824030d980004b00000001f04000
noncomputable def e137n_left : Nat → Nat
  | 0 => e137n_left_0
  | _ => 0
noncomputable def e137n_right_0 : Nat := 0x300201000
noncomputable def e137n_right : Nat → Nat
  | 0 => e137n_right_0
  | _ => 0
noncomputable def e137n_scale : Nat := 0x70000000002301000
noncomputable def e137n_target0 : Nat := 0x7ee1cff20151882400030d98000004b0000000002704000
noncomputable def e137n_target1 : Nat := 0x700000001b01000
noncomputable def e137n_target2 : Nat := 0x300201000
noncomputable def e137n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 123
  maxLength := 4
  maxWidth := 39
  terms := 1
  left := e137n_left
  right := e137n_right
  scale := e137n_scale
  target0 := e137n_target0
  target1 := e137n_target1
  target2 := e137n_target2

theorem e137n_ok : e137n.check=true := by decide +kernel
noncomputable def e137d_left_0 : Nat := 0x54f0000a02000
noncomputable def e137d_left : Nat → Nat
  | 0 => e137d_left_0
  | _ => 0
noncomputable def e137d_right_0 : Nat := 0x300201000
noncomputable def e137d_right : Nat → Nat
  | 0 => e137d_right_0
  | _ => 0
noncomputable def e137d_scale : Nat := 0x7000001301000
noncomputable def e137d_target0 : Nat := 0xfc807000001302000
noncomputable def e137d_target1 : Nat := 0x30000a01000
noncomputable def e137d_target2 : Nat := 0x300201000
noncomputable def e137d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 60
  maxLength := 2
  maxWidth := 19
  terms := 1
  left := e137d_left
  right := e137d_right
  scale := e137d_scale
  target0 := e137d_target0
  target1 := e137d_target1
  target2 := e137d_target2

theorem e137d_ok : e137d.check=true := by decide +kernel
noncomputable def e138n_left_0 : Nat := 0x3ffc7c056fb803df7dc8010cd86480002b0a200000064b0000000002b05000
noncomputable def e138n_left : Nat → Nat
  | 0 => e138n_left_0
  | _ => 0
noncomputable def e138n_right_0 : Nat := 0x300201000
noncomputable def e138n_right : Nat → Nat
  | 0 => e138n_right_0
  | _ => 0
noncomputable def e138n_scale : Nat := 0x34000000000002e01000
noncomputable def e138n_target0 : Nat := 0x3ffc7c056fb00803df7dc800010cd8648000002b0a20000000064b000000000003305000
noncomputable def e138n_target1 : Nat := 0x340000000002601000
noncomputable def e138n_target2 : Nat := 0x300201000
noncomputable def e138n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 159
  maxLength := 5
  maxWidth := 51
  terms := 1
  left := e138n_left
  right := e138n_right
  scale := e138n_scale
  target0 := e138n_target0
  target1 := e138n_target1
  target2 := e138n_target2

theorem e138n_ok : e138n.check=true := by decide +kernel
noncomputable def e138d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e138d_left : Nat → Nat
  | 0 => e138d_left_0
  | _ => 0
noncomputable def e138d_right_0 : Nat := 0x300201000
noncomputable def e138d_right : Nat → Nat
  | 0 => e138d_right_0
  | _ => 0
noncomputable def e138d_scale : Nat := 0xc00000000000003401000
noncomputable def e138d_target0 : Nat := 0x7f01731e38f001e55eca6a4000091edd260000002a06080000000001b00000000003400000000000003606000
noncomputable def e138d_target1 : Nat := 0x3000000000002a01000
noncomputable def e138d_target2 : Nat := 0x300201000
noncomputable def e138d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 169
  maxLength := 6
  maxWidth := 54
  terms := 1
  left := e138d_left
  right := e138d_right
  scale := e138d_scale
  target0 := e138d_target0
  target1 := e138d_target1
  target2 := e138d_target2

theorem e138d_ok : e138d.check=true := by decide +kernel
noncomputable def e139n_left_0 : Nat := 0x8001bff34c6e600b7f4c1cf007d6a3d4a800017249ee000000327340000000193000000000003206000
noncomputable def e139n_left : Nat → Nat
  | 0 => e139n_left_0
  | _ => 0
noncomputable def e139n_right_0 : Nat := 0x300201000
noncomputable def e139n_right : Nat → Nat
  | 0 => e139n_right_0
  | _ => 0
noncomputable def e139n_scale : Nat := 0x3400000000000003601000
noncomputable def e139n_target0 : Nat := 0x20006ffcd31b9004016fe9839e00007d6a3d4a8000000b924f7000000000c9cd000000000032600000000000003b06000
noncomputable def e139n_target1 : Nat := 0x1a000000000002d01000
noncomputable def e139n_target2 : Nat := 0x300201000
noncomputable def e139n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 184
  maxLength := 6
  maxWidth := 59
  terms := 1
  left := e139n_left
  right := e139n_right
  scale := e139n_scale
  target0 := e139n_target0
  target1 := e139n_target1
  target2 := e139n_target2

theorem e139n_ok : e139n.check=true := by decide +kernel
noncomputable def e139d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e139d_left : Nat → Nat
  | 0 => e139d_left_0
  | _ => 0
noncomputable def e139d_right_0 : Nat := 0x300201000
noncomputable def e139d_right : Nat → Nat
  | 0 => e139d_right_0
  | _ => 0
noncomputable def e139d_scale : Nat := 0xc00000000000003401000
noncomputable def e139d_target0 : Nat := 0x7f01731e38f001e55eca6a4000091edd260000002a06080000000001b00000000003400000000000003606000
noncomputable def e139d_target1 : Nat := 0x3000000000002a01000
noncomputable def e139d_target2 : Nat := 0x300201000
noncomputable def e139d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 169
  maxLength := 6
  maxWidth := 54
  terms := 1
  left := e139d_left
  right := e139d_right
  scale := e139d_scale
  target0 := e139d_target0
  target1 := e139d_target1
  target2 := e139d_target2

theorem e139d_ok : e139d.check=true := by decide +kernel
end ThomsonNegative.Certificate.Bridges.RFChecks
