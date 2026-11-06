import ThomsonNegative.Structure.Packed.IdentityKernel
namespace ThomsonNegative.Certificate.Bridges.RFChecks
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
noncomputable def e20n_left_0 : Nat := 0x200005d3821c7d580c6853bfff8c0893b6764c5585007fedb38545a06b903800010054461c8e6f2b90000002000cbb063af89000000003e29cf2648e60000000000791c7108580000000000016ebc1ed000000000000003c147f800000000000000029fd0000000000000000000570a000
noncomputable def e20n_left : Nat → Nat
  | 0 => e20n_left_0
  | _ => 0
noncomputable def e20n_right_0 : Nat := 0x300201000
noncomputable def e20n_right : Nat → Nat
  | 0 => e20n_right_0
  | _ => 0
noncomputable def e20n_scale : Nat := 0xf300000000000000000000005c01000
noncomputable def e20n_target0 : Nat := 0x200005d3821c7d580c6853800fffe30224ed9d931561400007fedb38545a06b903800000040151187239bcae4000000002000cbb063af8900000000000f8a73c992398000000000000791c710858000000000000005baf07b400000000000000003c147f8000000000000000000a7f4000000000000000000000610a000
noncomputable def e20n_target1 : Nat := 0x3cc00000000000000000005201000
noncomputable def e20n_target2 : Nat := 0x300201000
noncomputable def e20n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 300
  maxLength := 10
  maxWidth := 97
  terms := 1
  left := e20n_left
  right := e20n_right
  scale := e20n_scale
  target0 := e20n_target0
  target1 := e20n_target1
  target2 := e20n_target2

theorem e20n_ok : e20n.check=true := by decide +kernel
noncomputable def e20d_left_0 : Nat := 0x7fd9b08916d981c43d5a2f0096a20c6a000067deae0000001f6d00000000f3000000000003006000
noncomputable def e20d_left : Nat → Nat
  | 0 => e20d_left_0
  | _ => 0
noncomputable def e20d_right_0 : Nat := 0x300201000
noncomputable def e20d_right : Nat → Nat
  | 0 => e20d_right_0
  | _ => 0
noncomputable def e20d_scale : Nat := 0x3000000000000003601000
noncomputable def e20d_target0 : Nat := 0x7fd9b08916d900081c43d5a2f0000096a20c6a000000067deae0000000001f6d00000000000f3000000000000003c06000
noncomputable def e20d_target1 : Nat := 0x3000000000002a01000
noncomputable def e20d_target2 : Nat := 0x300201000
noncomputable def e20d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 187
  maxLength := 6
  maxWidth := 60
  terms := 1
  left := e20d_left
  right := e20d_right
  scale := e20d_scale
  target0 := e20d_target0
  target1 := e20d_target1
  target2 := e20d_target2

theorem e20d_ok : e20d.check=true := by decide +kernel
noncomputable def e21n_left_0 : Nat := 0x3ffff9483ff345eabcd7ffe2191c5869ad70010013b375adba1300002084e8c60e12400000043f49bfc0ee000000005dbfe5f1000000000003484430000000000001e87c0000000000000046d000000000000000004b09000
noncomputable def e21n_left : Nat → Nat
  | 0 => e21n_left_0
  | _ => 0
noncomputable def e21n_right_0 : Nat := 0x300201000
noncomputable def e21n_right : Nat → Nat
  | 0 => e21n_right_0
  | _ => 0
noncomputable def e21n_scale : Nat := 0x79800000000000000000005301000
noncomputable def e21n_target0 : Nat := 0x1ffffca41ff9a2f55e68007ffe2191c5869ad7000002002766eb5b742600000008213a318384900000000021fa4dfe077000000000005dbfe5f1000000000000006908860000000000000007a1f00000000000000000236800000000000000000005609000
noncomputable def e21n_target1 : Nat := 0xf3000000000000000004801000
noncomputable def e21n_target2 : Nat := 0x300201000
noncomputable def e21n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 267
  maxLength := 9
  maxWidth := 86
  terms := 1
  left := e21n_left
  right := e21n_right
  scale := e21n_scale
  target0 := e21n_target0
  target1 := e21n_target1
  target2 := e21n_target2

theorem e21n_ok : e21n.check=true := by decide +kernel
noncomputable def e21d_left_0 : Nat := 0x7fd9b08916d981c43d5a2f0096a20c6a000067deae0000001f6d00000000f3000000000003006000
noncomputable def e21d_left : Nat → Nat
  | 0 => e21d_left_0
  | _ => 0
noncomputable def e21d_right_0 : Nat := 0x300201000
noncomputable def e21d_right : Nat → Nat
  | 0 => e21d_right_0
  | _ => 0
noncomputable def e21d_scale : Nat := 0x1800000000000003501000
noncomputable def e21d_target0 : Nat := 0x1ff66c2245b640040e21ead178000096a20c6a0000000cfbd5c0000000007db4000000000079800000000000003b06000
noncomputable def e21d_target1 : Nat := 0x3000000000002a01000
noncomputable def e21d_target2 : Nat := 0x300201000
noncomputable def e21d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 184
  maxLength := 6
  maxWidth := 59
  terms := 1
  left := e21d_left
  right := e21d_right
  scale := e21d_scale
  target0 := e21d_target0
  target1 := e21d_target1
  target2 := e21d_target2

theorem e21d_ok : e21d.check=true := by decide +kernel
noncomputable def e22n_left_0 : Nat := 0x7fffcf2c6ebb6fa26d7ffdeecd27b6bd08008031d138c7dbdc000082f65bf77e580000008632e8c67e000000004ce4397800000000001615bc000000000000b0a8000000000000007d000000000000000004809000
noncomputable def e22n_left : Nat → Nat
  | 0 => e22n_left_0
  | _ => 0
noncomputable def e22n_right_0 : Nat := 0x300201000
noncomputable def e22n_right : Nat → Nat
  | 0 => e22n_right_0
  | _ => 0
noncomputable def e22n_scale : Nat := 0x79800000000000000000005301000
noncomputable def e22n_target0 : Nat := 0x1ffff3cb1baedbe89b40007ffdeecd27b6bd0800000200c744e31f6f70000000082f65bf77e58000000000218cba319f8000000000004ce43978000000000000005856f0000000000000000b0a8000000000000000001f4000000000000000000005609000
noncomputable def e22n_target1 : Nat := 0x1e600000000000000004501000
noncomputable def e22n_target2 : Nat := 0x300201000
noncomputable def e22n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 267
  maxLength := 9
  maxWidth := 86
  terms := 1
  left := e22n_left
  right := e22n_right
  scale := e22n_scale
  target0 := e22n_target0
  target1 := e22n_target1
  target2 := e22n_target2

theorem e22n_ok : e22n.check=true := by decide +kernel
noncomputable def e22d_left_0 : Nat := 0x7fd9b08916d981c43d5a2f0096a20c6a000067deae0000001f6d00000000f3000000000003006000
noncomputable def e22d_left : Nat → Nat
  | 0 => e22d_left_0
  | _ => 0
noncomputable def e22d_right_0 : Nat := 0x300201000
noncomputable def e22d_right : Nat → Nat
  | 0 => e22d_right_0
  | _ => 0
noncomputable def e22d_scale : Nat := 0x1800000000000003501000
noncomputable def e22d_target0 : Nat := 0x1ff66c2245b640040e21ead178000096a20c6a0000000cfbd5c0000000007db4000000000079800000000000003b06000
noncomputable def e22d_target1 : Nat := 0x3000000000002a01000
noncomputable def e22d_target2 : Nat := 0x300201000
noncomputable def e22d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 184
  maxLength := 6
  maxWidth := 59
  terms := 1
  left := e22d_left
  right := e22d_right
  scale := e22d_scale
  target0 := e22d_target0
  target1 := e22d_target1
  target2 := e22d_target2

theorem e22d_ok : e22d.check=true := by decide +kernel
noncomputable def e23n_left_0 : Nat := 0x200000ece28f0401a447e70d7fffce1a898b5b653befd801fff4aadd6bded19c5a1000080167308fda304c12000000201b6ae1d08f050a00000000815c172b783310000000000214ad1ede4fa000000000000591176df20000000000000005a5102900000000000000008194d80000000000000000023250000000000000000000005e0b000
noncomputable def e23n_left : Nat → Nat
  | 0 => e23n_left_0
  | _ => 0
noncomputable def e23n_right_0 : Nat := 0x300201000
noncomputable def e23n_right : Nat → Nat
  | 0 => e23n_right_0
  | _ => 0
noncomputable def e23n_scale : Nat := 0xf30000000000000000000000006401000
noncomputable def e23n_target0 : Nat := 0x400001d9c51e0803488fce1a001ffff386a262d6d94efbf600000fffa556eb5ef68ce2d0800000080167308fda304c120000000004036d5c3a11e0a140000000000205705cade0cc400000000000010a568f6f27d000000000000000591176df2000000000000000000b4a2052000000000000000000206536000000000000000000001192800000000000000000000000690b000
noncomputable def e23n_target1 : Nat := 0x1e60000000000000000000005901000
noncomputable def e23n_target2 : Nat := 0x300201000
noncomputable def e23n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 325
  maxLength := 11
  maxWidth := 105
  terms := 1
  left := e23n_left
  right := e23n_right
  scale := e23n_scale
  target0 := e23n_target0
  target1 := e23n_target1
  target2 := e23n_target2

theorem e23n_ok : e23n.check=true := by decide +kernel
noncomputable def e23d_left_0 : Nat := 0x7fd9b08916d981c43d5a2f0096a20c6a000067deae0000001f6d00000000f3000000000003006000
noncomputable def e23d_left : Nat → Nat
  | 0 => e23d_left_0
  | _ => 0
noncomputable def e23d_right_0 : Nat := 0x300201000
noncomputable def e23d_right : Nat → Nat
  | 0 => e23d_right_0
  | _ => 0
noncomputable def e23d_scale : Nat := 0x3000000000000003601000
noncomputable def e23d_target0 : Nat := 0x7fd9b08916d900081c43d5a2f0000096a20c6a000000067deae0000000001f6d00000000000f3000000000000003c06000
noncomputable def e23d_target1 : Nat := 0x3000000000002a01000
noncomputable def e23d_target2 : Nat := 0x300201000
noncomputable def e23d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 187
  maxLength := 6
  maxWidth := 60
  terms := 1
  left := e23d_left
  right := e23d_right
  scale := e23d_scale
  target0 := e23d_target0
  target1 := e23d_target1
  target2 := e23d_target2

theorem e23d_ok : e23d.check=true := by decide +kernel
noncomputable def e24n_left_0 : Nat := 0x1ffffe71712db702d1a3ecc0000dff69f2a296a4fb008006d6165db751e3c8000100036587cffbbc70000001fe5aa10b493f70000000041a1cb78321a000000000089567efba80000000000008bbf2930000000000000004bdc0800000000000000054830000000000000000000570a000
noncomputable def e24n_left : Nat → Nat
  | 0 => e24n_left_0
  | _ => 0
noncomputable def e24n_right_0 : Nat := 0x300201000
noncomputable def e24n_right : Nat → Nat
  | 0 => e24n_right_0
  | _ => 0
noncomputable def e24n_scale : Nat := 0xf300000000000000000000005c01000
noncomputable def e24n_target0 : Nat := 0x1ffffe71712db702d1a3ec801000037fda7ca8a5a93ec00008006d6165db751e3c80000004000d961f3feef1c000000001fe5aa10b493f70000000000106872de0c86800000000000089567efba80000000000000022efca4c000000000000000004bdc08000000000000000001520c000000000000000000000610a000
noncomputable def e24n_target1 : Nat := 0x3cc00000000000000000005201000
noncomputable def e24n_target2 : Nat := 0x300201000
noncomputable def e24n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 300
  maxLength := 10
  maxWidth := 97
  terms := 1
  left := e24n_left
  right := e24n_right
  scale := e24n_scale
  target0 := e24n_target0
  target1 := e24n_target1
  target2 := e24n_target2

theorem e24n_ok : e24n.check=true := by decide +kernel
noncomputable def e24d_left_0 : Nat := 0x7fd9b08916d981c43d5a2f0096a20c6a000067deae0000001f6d00000000f3000000000003006000
noncomputable def e24d_left : Nat → Nat
  | 0 => e24d_left_0
  | _ => 0
noncomputable def e24d_right_0 : Nat := 0x300201000
noncomputable def e24d_right : Nat → Nat
  | 0 => e24d_right_0
  | _ => 0
noncomputable def e24d_scale : Nat := 0x3000000000000003601000
noncomputable def e24d_target0 : Nat := 0x7fd9b08916d900081c43d5a2f0000096a20c6a000000067deae0000000001f6d00000000000f3000000000000003c06000
noncomputable def e24d_target1 : Nat := 0x3000000000002a01000
noncomputable def e24d_target2 : Nat := 0x300201000
noncomputable def e24d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 187
  maxLength := 6
  maxWidth := 60
  terms := 1
  left := e24d_left
  right := e24d_right
  scale := e24d_scale
  target0 := e24d_target0
  target1 := e24d_target1
  target2 := e24d_target2

theorem e24d_ok : e24d.check=true := by decide +kernel
noncomputable def e25n_left_0 : Nat := 0x80000f1bcfefea03a90780014100b6ccadc485007feaff584df0c69c00007de4e35ecfb9e4000000790136359d5200000000a37e3cabe60000000000e0bdcaac0000000000008200b4000000000000007d5f00000000000000007d0000000000000000000500a000
noncomputable def e25n_left : Nat → Nat
  | 0 => e25n_left_0
  | _ => 0
noncomputable def e25n_right_0 : Nat := 0x300201000
noncomputable def e25n_right : Nat → Nat
  | 0 => e25n_right_0
  | _ => 0
noncomputable def e25n_scale : Nat := 0x7980000000000000000000005b01000
noncomputable def e25n_target0 : Nat := 0x80000f1bcfefea03a907000200050402db32b71214000007feaff584df0c69c00000001f7938d7b3ee790000000000790136359d520000000000028df8f2af980000000000000e0bdcaac00000000000000020802d0000000000000000007d5f00000000000000000001f400000000000000000000005e0a000
noncomputable def e25n_target1 : Nat := 0x1e60000000000000000004d01000
noncomputable def e25n_target2 : Nat := 0x300201000
noncomputable def e25n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 291
  maxLength := 10
  maxWidth := 94
  terms := 1
  left := e25n_left
  right := e25n_right
  scale := e25n_scale
  target0 := e25n_target0
  target1 := e25n_target1
  target2 := e25n_target2

theorem e25n_ok : e25n.check=true := by decide +kernel
noncomputable def e25d_left_0 : Nat := 0x7fd9b08916d981c43d5a2f0096a20c6a000067deae0000001f6d00000000f3000000000003006000
noncomputable def e25d_left : Nat → Nat
  | 0 => e25d_left_0
  | _ => 0
noncomputable def e25d_right_0 : Nat := 0x300201000
noncomputable def e25d_right : Nat → Nat
  | 0 => e25d_right_0
  | _ => 0
noncomputable def e25d_scale : Nat := 0x1800000000000003501000
noncomputable def e25d_target0 : Nat := 0x1ff66c2245b640040e21ead178000096a20c6a0000000cfbd5c0000000007db4000000000079800000000000003b06000
noncomputable def e25d_target1 : Nat := 0x3000000000002a01000
noncomputable def e25d_target2 : Nat := 0x300201000
noncomputable def e25d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 184
  maxLength := 6
  maxWidth := 59
  terms := 1
  left := e25d_left
  right := e25d_right
  scale := e25d_scale
  target0 := e25d_target0
  target1 := e25d_target1
  target2 := e25d_target2

theorem e25d_ok : e25d.check=true := by decide +kernel
noncomputable def e26n_left_0 : Nat := 0x2000005584fb465c9770cc0005d023073de90ebb007ffd1af1fbf40e5c80000fdce5c2c7812870000001ea9a7054fdb7000000004a040905a9a0000000000c41d655a8000000000000e6ac5300000000000000189e080000000000000004430000000000000000000530a000
noncomputable def e26n_left : Nat → Nat
  | 0 => e26n_left_0
  | _ => 0
noncomputable def e26n_right_0 : Nat := 0x300201000
noncomputable def e26n_right : Nat → Nat
  | 0 => e26n_right_0
  | _ => 0
noncomputable def e26n_scale : Nat := 0x7980000000000000000000005b01000
noncomputable def e26n_target0 : Nat := 0x2000005584fb465c9770c80040005d023073de90ebb000007ffd1af1fbf40e5c80000000fdce5c2c7812870000000001ea9a7054fdb7000000000004a040905a9a0000000000000c41d655a8000000000000000e6ac5300000000000000000189e0800000000000000000044300000000000000000000005f0a000
noncomputable def e26n_target1 : Nat := 0x7980000000000000000004f01000
noncomputable def e26n_target2 : Nat := 0x300201000
noncomputable def e26n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 294
  maxLength := 10
  maxWidth := 95
  terms := 1
  left := e26n_left
  right := e26n_right
  scale := e26n_scale
  target0 := e26n_target0
  target1 := e26n_target1
  target2 := e26n_target2

theorem e26n_ok : e26n.check=true := by decide +kernel
noncomputable def e26d_left_0 : Nat := 0x7fd9b08916d981c43d5a2f0096a20c6a000067deae0000001f6d00000000f3000000000003006000
noncomputable def e26d_left : Nat → Nat
  | 0 => e26d_left_0
  | _ => 0
noncomputable def e26d_right_0 : Nat := 0x300201000
noncomputable def e26d_right : Nat → Nat
  | 0 => e26d_right_0
  | _ => 0
noncomputable def e26d_scale : Nat := 0x1800000000000003501000
noncomputable def e26d_target0 : Nat := 0x1ff66c2245b640040e21ead178000096a20c6a0000000cfbd5c0000000007db4000000000079800000000000003b06000
noncomputable def e26d_target1 : Nat := 0x3000000000002a01000
noncomputable def e26d_target2 : Nat := 0x300201000
noncomputable def e26d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 184
  maxLength := 6
  maxWidth := 59
  terms := 1
  left := e26d_left
  right := e26d_right
  scale := e26d_scale
  target0 := e26d_target0
  target1 := e26d_target1
  target2 := e26d_target2

theorem e26d_ok : e26d.check=true := by decide +kernel
noncomputable def e27n_left_0 : Nat := 0x404fa995187b96d800dfcd800008600000050000000002305000
noncomputable def e27n_left : Nat → Nat
  | 0 => e27n_left_0
  | _ => 0
noncomputable def e27n_right_0 : Nat := 0x300201000
noncomputable def e27n_right : Nat → Nat
  | 0 => e27n_right_0
  | _ => 0
noncomputable def e27n_scale : Nat := 0x3000000000002a01000
noncomputable def e27n_target0 : Nat := 0x1013ea65440087b96d8000037f360000000860000000014000000000002d05000
noncomputable def e27n_target1 : Nat := 0xc000000002001000
noncomputable def e27n_target2 : Nat := 0x300201000
noncomputable def e27n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 141
  maxLength := 5
  maxWidth := 45
  terms := 1
  left := e27n_left
  right := e27n_right
  scale := e27n_scale
  target0 := e27n_target0
  target1 := e27n_target1
  target2 := e27n_target2

theorem e27n_ok : e27n.check=true := by decide +kernel
noncomputable def e27d_left_0 : Nat := 0x300201000
noncomputable def e27d_left : Nat → Nat
  | 0 => e27d_left_0
  | _ => 0
noncomputable def e27d_right_0 : Nat := 0x300201000
noncomputable def e27d_right : Nat → Nat
  | 0 => e27d_right_0
  | _ => 0
noncomputable def e27d_scale : Nat := 0x30000a01000
noncomputable def e27d_target0 : Nat := 0x30000a01000
noncomputable def e27d_target1 : Nat := 0x300201000
noncomputable def e27d_target2 : Nat := 0x300201000
noncomputable def e27d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 30
  maxLength := 1
  maxWidth := 10
  terms := 1
  left := e27d_left
  right := e27d_right
  scale := e27d_scale
  target0 := e27d_target0
  target1 := e27d_target1
  target2 := e27d_target2

theorem e27d_ok : e27d.check=true := by decide +kernel
noncomputable def e28n_left_0 : Nat := 0x8000505f2cab921736fff5a20e267504bc01ff641de0e95cf80003fc5aca26bb30000007c9c0f804200000000b66e0ef40000000000b137280000000000031210000000000000004708000
noncomputable def e28n_left : Nat → Nat
  | 0 => e28n_left_0
  | _ => 0
noncomputable def e28n_right_0 : Nat := 0x300201000
noncomputable def e28n_right : Nat → Nat
  | 0 => e28n_right_0
  | _ => 0
noncomputable def e28n_scale : Nat := 0x798000000000000000004b01000
noncomputable def e28n_target0 : Nat := 0x8000505f2cab92173600fff5a20e267504bc0001ff641de0e95cf8000003fc5aca26bb3000000007c9c0f80420000000000b66e0ef4000000000000b1372800000000000003121000000000000000004f08000
noncomputable def e28n_target1 : Nat := 0x7980000000000000004301000
noncomputable def e28n_target2 : Nat := 0x300201000
noncomputable def e28n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 246
  maxLength := 8
  maxWidth := 79
  terms := 1
  left := e28n_left
  right := e28n_right
  scale := e28n_scale
  target0 := e28n_target0
  target1 := e28n_target1
  target2 := e28n_target2

theorem e28n_ok : e28n.check=true := by decide +kernel
noncomputable def e28d_left_0 : Nat := 0x7ff3943c72685b806c506d541600891ac7608d00008ecf3ed4000000488f050000000044b60000000000f300000000000003807000
noncomputable def e28d_left : Nat → Nat
  | 0 => e28d_left_0
  | _ => 0
noncomputable def e28d_right_0 : Nat := 0x300201000
noncomputable def e28d_right : Nat → Nat
  | 0 => e28d_right_0
  | _ => 0
noncomputable def e28d_scale : Nat := 0x180000000000000003d01000
noncomputable def e28d_target0 : Nat := 0xffe72878e4d0b600201b141b550580000448d63b04680000008ecf3ed4000000000911e0a0000000000112d80000000000007980000000000000004307000
noncomputable def e28d_target1 : Nat := 0x300000000000003201000
noncomputable def e28d_target2 : Nat := 0x300201000
noncomputable def e28d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 209
  maxLength := 7
  maxWidth := 67
  terms := 1
  left := e28d_left
  right := e28d_right
  scale := e28d_scale
  target0 := e28d_target0
  target1 := e28d_target1
  target2 := e28d_target2

theorem e28d_ok : e28d.check=true := by decide +kernel
noncomputable def e29n_left_0 : Nat := 0x1fffffedfff744de35d97ffefe1d3200b0fa60020019a0e100053dc00007ff607102da3a000000201437ffb776000000009cfdaf16a0000000000352a191c000000000000b4d96000000000000002239000000000000000004e09000
noncomputable def e29n_left : Nat → Nat
  | 0 => e29n_left_0
  | _ => 0
noncomputable def e29n_right_0 : Nat := 0x300201000
noncomputable def e29n_right : Nat → Nat
  | 0 => e29n_right_0
  | _ => 0
noncomputable def e29n_scale : Nat := 0x79800000000000000000005301000
noncomputable def e29n_target0 : Nat := 0x3fffffdbffee89bc6bb2007ffefe1d3200b0fa600001000cd07080029ee0000001ffd81c40b68e80000000040286fff6eec00000000009cfdaf16a0000000000001a950c8e000000000000002d36580000000000000000447200000000000000000005709000
noncomputable def e29n_target1 : Nat := 0x3cc000000000000000004a01000
noncomputable def e29n_target2 : Nat := 0x300201000
noncomputable def e29n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 270
  maxLength := 9
  maxWidth := 87
  terms := 1
  left := e29n_left
  right := e29n_right
  scale := e29n_scale
  target0 := e29n_target0
  target1 := e29n_target1
  target2 := e29n_target2

theorem e29n_ok : e29n.check=true := by decide +kernel
noncomputable def e29d_left_0 : Nat := 0x7ff3943c72685b806c506d541600891ac7608d00008ecf3ed4000000488f050000000044b60000000000f300000000000003807000
noncomputable def e29d_left : Nat → Nat
  | 0 => e29d_left_0
  | _ => 0
noncomputable def e29d_right_0 : Nat := 0x300201000
noncomputable def e29d_right : Nat → Nat
  | 0 => e29d_right_0
  | _ => 0
noncomputable def e29d_scale : Nat := 0x180000000000000003d01000
noncomputable def e29d_target0 : Nat := 0xffe72878e4d0b600201b141b550580000448d63b04680000008ecf3ed4000000000911e0a0000000000112d80000000000007980000000000000004307000
noncomputable def e29d_target1 : Nat := 0x300000000000003201000
noncomputable def e29d_target2 : Nat := 0x300201000
noncomputable def e29d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 209
  maxLength := 7
  maxWidth := 67
  terms := 1
  left := e29d_left
  right := e29d_right
  scale := e29d_scale
  target0 := e29d_target0
  target1 := e29d_target1
  target2 := e29d_target2

theorem e29d_ok : e29d.check=true := by decide +kernel
end ThomsonNegative.Certificate.Bridges.RFChecks
