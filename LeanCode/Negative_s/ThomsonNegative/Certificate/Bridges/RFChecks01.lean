import ThomsonNegative.Structure.Packed.IdentityKernel
namespace ThomsonNegative.Certificate.Bridges.RFChecks
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
noncomputable def e10n_left_0 : Nat := 0x79ca61aab736142400a99b20000a8400000030000000002405000
noncomputable def e10n_left : Nat → Nat
  | 0 => e10n_left_0
  | _ => 0
noncomputable def e10n_right_0 : Nat := 0x300201000
noncomputable def e10n_right : Nat → Nat
  | 0 => e10n_right_0
  | _ => 0
noncomputable def e10n_scale : Nat := 0x63000000000002f01000
noncomputable def e10n_target0 : Nat := 0x79ca61aab0073614240000a99b2000000a84000000003000000000002c05000
noncomputable def e10n_target1 : Nat := 0x630000000002701000
noncomputable def e10n_target2 : Nat := 0x300201000
noncomputable def e10n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 147
  maxLength := 5
  maxWidth := 47
  terms := 1
  left := e10n_left
  right := e10n_right
  scale := e10n_scale
  target0 := e10n_target0
  target1 := e10n_target1
  target2 := e10n_target2

theorem e10n_ok : e10n.check=true := by decide +kernel
noncomputable def e10d_left_0 : Nat := 0x7edd0602f55e4401f8580006300000001f04000
noncomputable def e10d_left : Nat → Nat
  | 0 => e10d_left_0
  | _ => 0
noncomputable def e10d_right_0 : Nat := 0x300201000
noncomputable def e10d_right : Nat → Nat
  | 0 => e10d_right_0
  | _ => 0
noncomputable def e10d_scale : Nat := 0x30000000002201000
noncomputable def e10d_target0 : Nat := 0x7edd060200f55e440001f85800000630000000002704000
noncomputable def e10d_target1 : Nat := 0x300000001a01000
noncomputable def e10d_target2 : Nat := 0x300201000
noncomputable def e10d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 123
  maxLength := 4
  maxWidth := 39
  terms := 1
  left := e10d_left
  right := e10d_right
  scale := e10d_scale
  target0 := e10d_target0
  target1 := e10d_target1
  target2 := e10d_target2

theorem e10d_ok : e10d.check=true := by decide +kernel
noncomputable def e11n_left_0 : Nat := 0x2018ab5a50f9702241b074d007e1c04df000041c6628000002850e0000000019000000000003106000
noncomputable def e11n_left : Nat → Nat
  | 0 => e11n_left_0
  | _ => 0
noncomputable def e11n_right_0 : Nat := 0x300201000
noncomputable def e11n_right : Nat → Nat
  | 0 => e11n_right_0
  | _ => 0
noncomputable def e11n_scale : Nat := 0xc600000000000003801000
noncomputable def e11n_target0 : Nat := 0x2018ab5a50f960102241b074d00007e1c04df00000041c662800000002850e00000000001900000000000003906000
noncomputable def e11n_target1 : Nat := 0xc6000000000003001000
noncomputable def e11n_target2 : Nat := 0x300201000
noncomputable def e11n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 178
  maxLength := 6
  maxWidth := 57
  terms := 1
  left := e11n_left
  right := e11n_right
  scale := e11n_scale
  target0 := e11n_target0
  target1 := e11n_target1
  target2 := e11n_target2

theorem e11n_ok : e11n.check=true := by decide +kernel
noncomputable def e11d_left_0 : Nat := 0x7edd0602f55e4401f8580006300000001f04000
noncomputable def e11d_left : Nat → Nat
  | 0 => e11d_left_0
  | _ => 0
noncomputable def e11d_right_0 : Nat := 0x300201000
noncomputable def e11d_right : Nat → Nat
  | 0 => e11d_right_0
  | _ => 0
noncomputable def e11d_scale : Nat := 0x60000000002301000
noncomputable def e11d_target0 : Nat := 0x7edd0602007aaf2200007e16000000c60000000002804000
noncomputable def e11d_target1 : Nat := 0x300000001a01000
noncomputable def e11d_target2 : Nat := 0x300201000
noncomputable def e11d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 126
  maxLength := 4
  maxWidth := 40
  terms := 1
  left := e11d_left
  right := e11d_right
  scale := e11d_scale
  target0 := e11d_target0
  target1 := e11d_target1
  target2 := e11d_target2

theorem e11d_ok : e11d.check=true := by decide +kernel
noncomputable def e12n_left_0 : Nat := 0x7a47749ec659002230000300000001c04000
noncomputable def e12n_left : Nat → Nat
  | 0 => e12n_left_0
  | _ => 0
noncomputable def e12n_right_0 : Nat := 0x300201000
noncomputable def e12n_right : Nat → Nat
  | 0 => e12n_right_0
  | _ => 0
noncomputable def e12n_scale : Nat := 0x630000000002701000
noncomputable def e12n_target0 : Nat := 0x7a4774900ec659000022300000030000000002404000
noncomputable def e12n_target1 : Nat := 0x6300000001f01000
noncomputable def e12n_target2 : Nat := 0x300201000
noncomputable def e12n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 123
  maxLength := 4
  maxWidth := 39
  terms := 1
  left := e12n_left
  right := e12n_right
  scale := e12n_scale
  target0 := e12n_target0
  target1 := e12n_target1
  target2 := e12n_target2

theorem e12n_ok : e12n.check=true := by decide +kernel
noncomputable def e12d_left_0 : Nat := 0xf3cf6dc590063000001703000
noncomputable def e12d_left : Nat → Nat
  | 0 => e12d_left_0
  | _ => 0
noncomputable def e12d_right_0 : Nat := 0x300201000
noncomputable def e12d_right : Nat → Nat
  | 0 => e12d_right_0
  | _ => 0
noncomputable def e12d_scale : Nat := 0x300000001a01000
noncomputable def e12d_target0 : Nat := 0xf3cf6c01c5900006300000001f03000
noncomputable def e12d_target1 : Nat := 0x3000001201000
noncomputable def e12d_target2 : Nat := 0x300201000
noncomputable def e12d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 97
  maxLength := 3
  maxWidth := 31
  terms := 1
  left := e12d_left
  right := e12d_right
  scale := e12d_scale
  target0 := e12d_target0
  target1 := e12d_target1
  target2 := e12d_target2

theorem e12d_ok : e12d.check=true := by decide +kernel
noncomputable def e13n_left_0 : Nat := 0x101776516a980c536260042fe21800029cd8000000190000000002905000
noncomputable def e13n_left : Nat → Nat
  | 0 => e13n_left_0
  | _ => 0
noncomputable def e13n_right_0 : Nat := 0x300201000
noncomputable def e13n_right : Nat → Nat
  | 0 => e13n_right_0
  | _ => 0
noncomputable def e13n_scale : Nat := 0xc6000000000003001000
noncomputable def e13n_target0 : Nat := 0x101776516a90080c53626000042fe2180000029cd80000000019000000000003105000
noncomputable def e13n_target1 : Nat := 0xc60000000002801000
noncomputable def e13n_target2 : Nat := 0x300201000
noncomputable def e13n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 153
  maxLength := 5
  maxWidth := 49
  terms := 1
  left := e13n_left
  right := e13n_right
  scale := e13n_scale
  target0 := e13n_target0
  target1 := e13n_target1
  target2 := e13n_target2

theorem e13n_ok : e13n.check=true := by decide +kernel
noncomputable def e13d_left_0 : Nat := 0xf3cf6dc590063000001703000
noncomputable def e13d_left : Nat → Nat
  | 0 => e13d_left_0
  | _ => 0
noncomputable def e13d_right_0 : Nat := 0x300201000
noncomputable def e13d_right : Nat → Nat
  | 0 => e13d_right_0
  | _ => 0
noncomputable def e13d_scale : Nat := 0x600000001b01000
noncomputable def e13d_target0 : Nat := 0x79e7b60071640000c600000002003000
noncomputable def e13d_target1 : Nat := 0x3000001201000
noncomputable def e13d_target2 : Nat := 0x300201000
noncomputable def e13d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 100
  maxLength := 3
  maxWidth := 32
  terms := 1
  left := e13d_left
  right := e13d_right
  scale := e13d_scale
  target0 := e13d_target0
  target1 := e13d_target1
  target2 := e13d_target2

theorem e13d_ok : e13d.check=true := by decide +kernel
noncomputable def e14n_left_0 : Nat := 0x87b289260585900348c0001b00000001e04000
noncomputable def e14n_left : Nat → Nat
  | 0 => e14n_left_0
  | _ => 0
noncomputable def e14n_right_0 : Nat := 0x300201000
noncomputable def e14n_right : Nat → Nat
  | 0 => e14n_right_0
  | _ => 0
noncomputable def e14n_scale : Nat := 0x630000000002701000
noncomputable def e14n_target0 : Nat := 0x87b2892402058590000348c000001b0000000002604000
noncomputable def e14n_target1 : Nat := 0x6300000001f01000
noncomputable def e14n_target2 : Nat := 0x300201000
noncomputable def e14n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 123
  maxLength := 4
  maxWidth := 39
  terms := 1
  left := e14n_left
  right := e14n_right
  scale := e14n_scale
  target0 := e14n_target0
  target1 := e14n_target1
  target2 := e14n_target2

theorem e14n_ok : e14n.check=true := by decide +kernel
noncomputable def e14d_left_0 : Nat := 0xf3cf6dc590063000001703000
noncomputable def e14d_left : Nat → Nat
  | 0 => e14d_left_0
  | _ => 0
noncomputable def e14d_right_0 : Nat := 0x300201000
noncomputable def e14d_right : Nat → Nat
  | 0 => e14d_right_0
  | _ => 0
noncomputable def e14d_scale : Nat := 0x300000001a01000
noncomputable def e14d_target0 : Nat := 0xf3cf6c01c5900006300000001f03000
noncomputable def e14d_target1 : Nat := 0x3000001201000
noncomputable def e14d_target2 : Nat := 0x300201000
noncomputable def e14d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 97
  maxLength := 3
  maxWidth := 31
  terms := 1
  left := e14d_left
  right := e14d_right
  scale := e14d_scale
  target0 := e14d_target0
  target1 := e14d_target1
  target2 := e14d_target2

theorem e14d_ok : e14d.check=true := by decide +kernel
noncomputable def e15n_left_0 : Nat := 0xffaaaa48a981d7df26004a47a18000248d8000000190000000002905000
noncomputable def e15n_left : Nat → Nat
  | 0 => e15n_left_0
  | _ => 0
noncomputable def e15n_right_0 : Nat := 0x300201000
noncomputable def e15n_right : Nat → Nat
  | 0 => e15n_right_0
  | _ => 0
noncomputable def e15n_scale : Nat := 0xc6000000000003001000
noncomputable def e15n_target0 : Nat := 0xffaaaa48a90081d7df2600004a47a1800000248d80000000019000000000003105000
noncomputable def e15n_target1 : Nat := 0xc60000000002801000
noncomputable def e15n_target2 : Nat := 0x300201000
noncomputable def e15n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 153
  maxLength := 5
  maxWidth := 49
  terms := 1
  left := e15n_left
  right := e15n_right
  scale := e15n_scale
  target0 := e15n_target0
  target1 := e15n_target1
  target2 := e15n_target2

theorem e15n_ok : e15n.check=true := by decide +kernel
noncomputable def e15d_left_0 : Nat := 0xf3cf6dc590063000001703000
noncomputable def e15d_left : Nat → Nat
  | 0 => e15d_left_0
  | _ => 0
noncomputable def e15d_right_0 : Nat := 0x300201000
noncomputable def e15d_right : Nat → Nat
  | 0 => e15d_right_0
  | _ => 0
noncomputable def e15d_scale : Nat := 0x600000001b01000
noncomputable def e15d_target0 : Nat := 0x79e7b60071640000c600000002003000
noncomputable def e15d_target1 : Nat := 0x3000001201000
noncomputable def e15d_target2 : Nat := 0x300201000
noncomputable def e15d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 100
  maxLength := 3
  maxWidth := 32
  terms := 1
  left := e15d_left
  right := e15d_right
  scale := e15d_scale
  target0 := e15d_target0
  target1 := e15d_target1
  target2 := e15d_target2

theorem e15d_ok : e15d.check=true := by decide +kernel
noncomputable def e16n_left_0 : Nat := 0x7e192349c69a50c02b4a200001900000002104000
noncomputable def e16n_left : Nat → Nat
  | 0 => e16n_left_0
  | _ => 0
noncomputable def e16n_right_0 : Nat := 0x300201000
noncomputable def e16n_right : Nat → Nat
  | 0 => e16n_right_0
  | _ => 0
noncomputable def e16n_scale : Nat := 0x1a0000000002501000
noncomputable def e16n_target0 : Nat := 0x7e19234980469a50c0002b4a2000000190000000002904000
noncomputable def e16n_target1 : Nat := 0x1a00000001d01000
noncomputable def e16n_target2 : Nat := 0x300201000
noncomputable def e16n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 129
  maxLength := 4
  maxWidth := 41
  terms := 1
  left := e16n_left
  right := e16n_right
  scale := e16n_scale
  target0 := e16n_target0
  target1 := e16n_target1
  target2 := e16n_target2

theorem e16n_ok : e16n.check=true := by decide +kernel
noncomputable def e16d_left_0 : Nat := 0xb0ce9ea6009000001403000
noncomputable def e16d_left : Nat → Nat
  | 0 => e16d_left_0
  | _ => 0
noncomputable def e16d_right_0 : Nat := 0x300201000
noncomputable def e16d_right : Nat → Nat
  | 0 => e16d_right_0
  | _ => 0
noncomputable def e16d_scale : Nat := 0x1a00000001d01000
noncomputable def e16d_target0 : Nat := 0x9e811a00c27c00008a00000002003000
noncomputable def e16d_target1 : Nat := 0x3000001201000
noncomputable def e16d_target2 : Nat := 0x300201000
noncomputable def e16d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 100
  maxLength := 3
  maxWidth := 32
  terms := 1
  left := e16d_left
  right := e16d_right
  scale := e16d_scale
  target0 := e16d_target0
  target1 := e16d_target1
  target2 := e16d_target2

theorem e16d_ok : e16d.check=true := by decide +kernel
noncomputable def e17n_left_0 : Nat := 0x7ffe8308377e51ac78009f0f589b80eb008106ac226165b000081a2d35d9ff0000008430311e500000000527a2b100000000000fc39000000000000b250000000000000004408000
noncomputable def e17n_left : Nat → Nat
  | 0 => e17n_left_0
  | _ => 0
noncomputable def e17n_right_0 : Nat := 0x300201000
noncomputable def e17n_right : Nat → Nat
  | 0 => e17n_right_0
  | _ => 0
noncomputable def e17n_scale : Nat := 0x798000000000000000004b01000
noncomputable def e17n_target0 : Nat := 0x7ffe8308377e51ac70020027c3d626e03ac00008106ac226165b0000002068b4d767fc000000008430311e50000000000149e8ac40000000000000fc39000000000000002c94000000000000000004e08000
noncomputable def e17n_target1 : Nat := 0x1e60000000000000004101000
noncomputable def e17n_target2 : Nat := 0x300201000
noncomputable def e17n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 243
  maxLength := 8
  maxWidth := 78
  terms := 1
  left := e17n_left
  right := e17n_right
  scale := e17n_scale
  target0 := e17n_target0
  target1 := e17n_target1
  target2 := e17n_target2

theorem e17n_ok : e17n.check=true := by decide +kernel
noncomputable def e17d_left_0 : Nat := 0x7fd9b08916d981c43d5a2f0096a20c6a000067deae0000001f6d00000000f3000000000003006000
noncomputable def e17d_left : Nat → Nat
  | 0 => e17d_left_0
  | _ => 0
noncomputable def e17d_right_0 : Nat := 0x300201000
noncomputable def e17d_right : Nat → Nat
  | 0 => e17d_right_0
  | _ => 0
noncomputable def e17d_scale : Nat := 0x1800000000000003501000
noncomputable def e17d_target0 : Nat := 0x1ff66c2245b640040e21ead178000096a20c6a0000000cfbd5c0000000007db4000000000079800000000000003b06000
noncomputable def e17d_target1 : Nat := 0x3000000000002a01000
noncomputable def e17d_target2 : Nat := 0x300201000
noncomputable def e17d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 184
  maxLength := 6
  maxWidth := 59
  terms := 1
  left := e17d_left
  right := e17d_right
  scale := e17d_scale
  target0 := e17d_target0
  target1 := e17d_target1
  target2 := e17d_target2

theorem e17d_ok : e17d.check=true := by decide +kernel
noncomputable def e18n_left_0 : Nat := 0x3fffe69a08196102e6d80036ef3a74e8f67001002c5474326b5300001f53d899e45640000003ab5525b62e00000000a6b7122100000000001dd01430000000000001e93c0000000000000038d000000000000000004b09000
noncomputable def e18n_left : Nat → Nat
  | 0 => e18n_left_0
  | _ => 0
noncomputable def e18n_right_0 : Nat := 0x300201000
noncomputable def e18n_right : Nat → Nat
  | 0 => e18n_right_0
  | _ => 0
noncomputable def e18n_scale : Nat := 0x79800000000000000000005301000
noncomputable def e18n_target0 : Nat := 0x1ffff34d040cb08173680080036ef3a74e8f670000020058a8e864d6a600000007d4f626791590000000001d5aa92db1700000000000a6b7122100000000000003ba02860000000000000007a4f000000000000000001c6800000000000000000005609000
noncomputable def e18n_target1 : Nat := 0xf3000000000000000004801000
noncomputable def e18n_target2 : Nat := 0x300201000
noncomputable def e18n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 267
  maxLength := 9
  maxWidth := 86
  terms := 1
  left := e18n_left
  right := e18n_right
  scale := e18n_scale
  target0 := e18n_target0
  target1 := e18n_target1
  target2 := e18n_target2

theorem e18n_ok : e18n.check=true := by decide +kernel
noncomputable def e18d_left_0 : Nat := 0x7fd9b08916d981c43d5a2f0096a20c6a000067deae0000001f6d00000000f3000000000003006000
noncomputable def e18d_left : Nat → Nat
  | 0 => e18d_left_0
  | _ => 0
noncomputable def e18d_right_0 : Nat := 0x300201000
noncomputable def e18d_right : Nat → Nat
  | 0 => e18d_right_0
  | _ => 0
noncomputable def e18d_scale : Nat := 0x1800000000000003501000
noncomputable def e18d_target0 : Nat := 0x1ff66c2245b640040e21ead178000096a20c6a0000000cfbd5c0000000007db4000000000079800000000000003b06000
noncomputable def e18d_target1 : Nat := 0x3000000000002a01000
noncomputable def e18d_target2 : Nat := 0x300201000
noncomputable def e18d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 184
  maxLength := 6
  maxWidth := 59
  terms := 1
  left := e18d_left
  right := e18d_right
  scale := e18d_scale
  target0 := e18d_target0
  target1 := e18d_target1
  target2 := e18d_target2

theorem e18d_ok : e18d.check=true := by decide +kernel
noncomputable def e19n_left_0 : Nat := 0x800035fca03064b7780001bb8ca1c65b007fb1d3f303a4b00007d4a0ab90af0000007bd984af500000000b09f8010000000000e22890000000000005b50000000000000004408000
noncomputable def e19n_left : Nat → Nat
  | 0 => e19n_left_0
  | _ => 0
noncomputable def e19n_right_0 : Nat := 0x300201000
noncomputable def e19n_right : Nat → Nat
  | 0 => e19n_right_0
  | _ => 0
noncomputable def e19n_scale : Nat := 0x798000000000000000004b01000
noncomputable def e19n_target0 : Nat := 0x800035fca03064b7700200006ee3287196c00007fb1d3f303a4b0000001f5282ae42bc000000007bd984af500000000002c27e004000000000000e22890000000000000016d4000000000000000004e08000
noncomputable def e19n_target1 : Nat := 0x1e60000000000000004101000
noncomputable def e19n_target2 : Nat := 0x300201000
noncomputable def e19n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 243
  maxLength := 8
  maxWidth := 78
  terms := 1
  left := e19n_left
  right := e19n_right
  scale := e19n_scale
  target0 := e19n_target0
  target1 := e19n_target1
  target2 := e19n_target2

theorem e19n_ok : e19n.check=true := by decide +kernel
noncomputable def e19d_left_0 : Nat := 0x7fd9b08916d981c43d5a2f0096a20c6a000067deae0000001f6d00000000f3000000000003006000
noncomputable def e19d_left : Nat → Nat
  | 0 => e19d_left_0
  | _ => 0
noncomputable def e19d_right_0 : Nat := 0x300201000
noncomputable def e19d_right : Nat → Nat
  | 0 => e19d_right_0
  | _ => 0
noncomputable def e19d_scale : Nat := 0x1800000000000003501000
noncomputable def e19d_target0 : Nat := 0x1ff66c2245b640040e21ead178000096a20c6a0000000cfbd5c0000000007db4000000000079800000000000003b06000
noncomputable def e19d_target1 : Nat := 0x3000000000002a01000
noncomputable def e19d_target2 : Nat := 0x300201000
noncomputable def e19d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 184
  maxLength := 6
  maxWidth := 59
  terms := 1
  left := e19d_left
  right := e19d_right
  scale := e19d_scale
  target0 := e19d_target0
  target1 := e19d_target1
  target2 := e19d_target2

theorem e19d_ok : e19d.check=true := by decide +kernel
end ThomsonNegative.Certificate.Bridges.RFChecks
