import ThomsonNegative.Structure.Packed.IdentityKernel
namespace ThomsonNegative.Certificate.Bridges.RFChecks
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
noncomputable def e120n_left_0 : Nat := 0xfffc1088fb212dffa22f5a32b004195be63bd0000a3c511a800000194a1540000000263b00000000004300000000000003707000
noncomputable def e120n_left : Nat → Nat
  | 0 => e120n_left_0
  | _ => 0
noncomputable def e120n_right_0 : Nat := 0x300201000
noncomputable def e120n_right : Nat → Nat
  | 0 => e120n_right_0
  | _ => 0
noncomputable def e120n_scale : Nat := 0x340000000000000003e01000
noncomputable def e120n_target0 : Nat := 0xfffc1088fb212c001ffa22f5a32b000004195be63bd0000000a3c511a800000000194a1540000000000263b00000000000004300000000000000004307000
noncomputable def e120n_target1 : Nat := 0x340000000000003201000
noncomputable def e120n_target2 : Nat := 0x300201000
noncomputable def e120n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 209
  maxLength := 7
  maxWidth := 67
  terms := 1
  left := e120n_left
  right := e120n_right
  scale := e120n_scale
  target0 := e120n_target0
  target1 := e120n_target1
  target2 := e120n_target2

theorem e120n_ok : e120n.check=true := by decide +kernel
noncomputable def e120d_left_0 : Nat := 0xfceee18557a7676e00565d380000cf800000150000000002505000
noncomputable def e120d_left : Nat → Nat
  | 0 => e120d_left_0
  | _ => 0
noncomputable def e120d_right_0 : Nat := 0x300201000
noncomputable def e120d_right : Nat → Nat
  | 0 => e120d_right_0
  | _ => 0
noncomputable def e120d_scale : Nat := 0xc000000000002c01000
noncomputable def e120d_target0 : Nat := 0x3f3bb86154007a7676e000015974e0000000cf80000000054000000000002f05000
noncomputable def e120d_target1 : Nat := 0x30000000002201000
noncomputable def e120d_target2 : Nat := 0x300201000
noncomputable def e120d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 147
  maxLength := 5
  maxWidth := 47
  terms := 1
  left := e120d_left
  right := e120d_right
  scale := e120d_scale
  target0 := e120d_target0
  target1 := e120d_target1
  target2 := e120d_target2

theorem e120d_ok : e120d.check=true := by decide +kernel
noncomputable def e121n_left_0 : Nat := 0x3fffd372e401955ff4b2cb76e940104a74b5f430000a9d1dd36000000705a12c0000000221540000000000bd00000000000003907000
noncomputable def e121n_left : Nat → Nat
  | 0 => e121n_left_0
  | _ => 0
noncomputable def e121n_right_0 : Nat := 0x300201000
noncomputable def e121n_right : Nat → Nat
  | 0 => e121n_right_0
  | _ => 0
noncomputable def e121n_scale : Nat := 0x340000000000000003e01000
noncomputable def e121n_target0 : Nat := 0xffff4dcb900655001ff4b2cb76e9400004129d2d7d0c000000a9d1dd36000000001c1684b0000000000221540000000000002f40000000000000004307000
noncomputable def e121n_target1 : Nat := 0xd00000000000003401000
noncomputable def e121n_target2 : Nat := 0x300201000
noncomputable def e121n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 209
  maxLength := 7
  maxWidth := 67
  terms := 1
  left := e121n_left
  right := e121n_right
  scale := e121n_scale
  target0 := e121n_target0
  target1 := e121n_target1
  target2 := e121n_target2

theorem e121n_ok : e121n.check=true := by decide +kernel
noncomputable def e121d_left_0 : Nat := 0xfceee18557a7676e00565d380000cf800000150000000002505000
noncomputable def e121d_left : Nat → Nat
  | 0 => e121d_left_0
  | _ => 0
noncomputable def e121d_right_0 : Nat := 0x300201000
noncomputable def e121d_right : Nat → Nat
  | 0 => e121d_right_0
  | _ => 0
noncomputable def e121d_scale : Nat := 0xc000000000002c01000
noncomputable def e121d_target0 : Nat := 0x3f3bb86154007a7676e000015974e0000000cf80000000054000000000002f05000
noncomputable def e121d_target1 : Nat := 0x30000000002201000
noncomputable def e121d_target2 : Nat := 0x300201000
noncomputable def e121d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 147
  maxLength := 5
  maxWidth := 47
  terms := 1
  left := e121d_left
  right := e121d_right
  scale := e121d_scale
  target0 := e121d_target0
  target1 := e121d_target1
  target2 := e121d_target2

theorem e121d_ok : e121d.check=true := by decide +kernel
noncomputable def e122n_left_0 : Nat := 0x80af2a0dda333003e840000900000001e04000
noncomputable def e122n_left : Nat → Nat
  | 0 => e122n_left_0
  | _ => 0
noncomputable def e122n_right_0 : Nat := 0x300201000
noncomputable def e122n_right : Nat → Nat
  | 0 => e122n_right_0
  | _ => 0
noncomputable def e122n_scale : Nat := 0x30000000002201000
noncomputable def e122n_target0 : Nat := 0x80af2a0c00ed19980000fa1000000120000000002704000
noncomputable def e122n_target1 : Nat := 0x180000001901000
noncomputable def e122n_target2 : Nat := 0x300201000
noncomputable def e122n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 123
  maxLength := 4
  maxWidth := 39
  terms := 1
  left := e122n_left
  right := e122n_right
  scale := e122n_scale
  target0 := e122n_target0
  target1 := e122n_target1
  target2 := e122n_target2

theorem e122n_ok : e122n.check=true := by decide +kernel
noncomputable def e122d_left_0 : Nat := 0x54f0000a02000
noncomputable def e122d_left : Nat → Nat
  | 0 => e122d_left_0
  | _ => 0
noncomputable def e122d_right_0 : Nat := 0x300201000
noncomputable def e122d_right : Nat → Nat
  | 0 => e122d_right_0
  | _ => 0
noncomputable def e122d_scale : Nat := 0x3000001201000
noncomputable def e122d_target0 : Nat := 0x54c03000001202000
noncomputable def e122d_target1 : Nat := 0x30000a01000
noncomputable def e122d_target2 : Nat := 0x300201000
noncomputable def e122d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 57
  maxLength := 2
  maxWidth := 18
  terms := 1
  left := e122d_left
  right := e122d_right
  scale := e122d_scale
  target0 := e122d_target0
  target1 := e122d_target1
  target2 := e122d_target2

theorem e122d_ok : e122d.check=true := by decide +kernel
noncomputable def e123n_left_0 : Nat := 0xffe38deae81ec85fef207c129f10041fa4221d970000987eeae78000001a6767fc0000000278e1000000000046900000000000003b07000
noncomputable def e123n_left : Nat → Nat
  | 0 => e123n_left_0
  | _ => 0
noncomputable def e123n_right_0 : Nat := 0x300201000
noncomputable def e123n_right : Nat → Nat
  | 0 => e123n_right_0
  | _ => 0
noncomputable def e123n_scale : Nat := 0x7c0000000000000003f01000
noncomputable def e123n_target0 : Nat := 0x7ff1c6f5740f642007fbc81f04a7c4000083f48443b2e000000987eeae7800000000d33b3fe00000000009e3840000000000008d20000000000000004407000
noncomputable def e123n_target1 : Nat := 0x3e00000000000003601000
noncomputable def e123n_target2 : Nat := 0x300201000
noncomputable def e123n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 212
  maxLength := 7
  maxWidth := 68
  terms := 1
  left := e123n_left
  right := e123n_right
  scale := e123n_scale
  target0 := e123n_target0
  target1 := e123n_target1
  target2 := e123n_target2

theorem e123n_ok : e123n.check=true := by decide +kernel
noncomputable def e123d_left_0 : Nat := 0xfceee18557a7676e00565d380000cf800000150000000002505000
noncomputable def e123d_left : Nat → Nat
  | 0 => e123d_left_0
  | _ => 0
noncomputable def e123d_right_0 : Nat := 0x300201000
noncomputable def e123d_right : Nat → Nat
  | 0 => e123d_right_0
  | _ => 0
noncomputable def e123d_scale : Nat := 0x1c000000000002d01000
noncomputable def e123d_target0 : Nat := 0x7db32923fc0077b1b2500000c317a80000000dd000000000bc000000000003005000
noncomputable def e123d_target1 : Nat := 0x30000000002201000
noncomputable def e123d_target2 : Nat := 0x300201000
noncomputable def e123d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 150
  maxLength := 5
  maxWidth := 48
  terms := 1
  left := e123d_left
  right := e123d_right
  scale := e123d_scale
  target0 := e123d_target0
  target1 := e123d_target1
  target2 := e123d_target2

theorem e123d_ok : e123d.check=true := by decide +kernel
noncomputable def e124n_left_0 : Nat := 0x7fff27a8fc3da262e0044c026df1b5f007f8725f6b533c0001b2cb830923000000363b4ebc40000000122e94d0000000000663d4000000000001f10000000000000004208000
noncomputable def e124n_left : Nat → Nat
  | 0 => e124n_left_0
  | _ => 0
noncomputable def e124n_right_0 : Nat := 0x300201000
noncomputable def e124n_right : Nat → Nat
  | 0 => e124n_right_0
  | _ => 0
noncomputable def e124n_scale : Nat := 0x7c000000000000000004701000
noncomputable def e124n_target0 : Nat := 0x7fff27a8fc3da262c0080113009b7c6d7c00007f8725f6b533c0000006cb2e0c248c00000000363b4ebc4000000000048ba534000000000000663d4000000000000007c4000000000000000004c08000
noncomputable def e124n_target1 : Nat := 0x1f0000000000000003d01000
noncomputable def e124n_target2 : Nat := 0x300201000
noncomputable def e124n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 237
  maxLength := 8
  maxWidth := 76
  terms := 1
  left := e124n_left
  right := e124n_right
  scale := e124n_scale
  target0 := e124n_target0
  target1 := e124n_target1
  target2 := e124n_target2

theorem e124n_ok : e124n.check=true := by decide +kernel
noncomputable def e124d_left_0 : Nat := 0xfceee18557a7676e00565d380000cf800000150000000002505000
noncomputable def e124d_left : Nat → Nat
  | 0 => e124d_left_0
  | _ => 0
noncomputable def e124d_right_0 : Nat := 0x300201000
noncomputable def e124d_right : Nat → Nat
  | 0 => e124d_right_0
  | _ => 0
noncomputable def e124d_scale : Nat := 0x1c000000000002d01000
noncomputable def e124d_target0 : Nat := 0x7db32923fc0077b1b2500000c317a80000000dd000000000bc000000000003005000
noncomputable def e124d_target1 : Nat := 0x30000000002201000
noncomputable def e124d_target2 : Nat := 0x300201000
noncomputable def e124d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 150
  maxLength := 5
  maxWidth := 48
  terms := 1
  left := e124d_left
  right := e124d_right
  scale := e124d_scale
  target0 := e124d_target0
  target1 := e124d_target1
  target2 := e124d_target2

theorem e124d_ok : e124d.check=true := by decide +kernel
noncomputable def e125n_left_0 : Nat := 0x40022a538354766010f5d19d76400fd70f426bf0000647e410e000000159de1c00000001642400000000010100000000000003907000
noncomputable def e125n_left : Nat → Nat
  | 0 => e125n_left_0
  | _ => 0
noncomputable def e125n_right_0 : Nat := 0x300201000
noncomputable def e125n_right : Nat → Nat
  | 0 => e125n_right_0
  | _ => 0
noncomputable def e125n_scale : Nat := 0x7c0000000000000003f01000
noncomputable def e125n_target0 : Nat := 0x800454a706a8ec8008043d74675d9000007eb87a135f8000000647e410e0000000002b3bc380000000000590900000000000008080000000000000004407000
noncomputable def e125n_target1 : Nat := 0xf80000000000003401000
noncomputable def e125n_target2 : Nat := 0x300201000
noncomputable def e125n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 212
  maxLength := 7
  maxWidth := 68
  terms := 1
  left := e125n_left
  right := e125n_right
  scale := e125n_scale
  target0 := e125n_target0
  target1 := e125n_target1
  target2 := e125n_target2

theorem e125n_ok : e125n.check=true := by decide +kernel
noncomputable def e125d_left_0 : Nat := 0xfceee18557a7676e00565d380000cf800000150000000002505000
noncomputable def e125d_left : Nat → Nat
  | 0 => e125d_left_0
  | _ => 0
noncomputable def e125d_right_0 : Nat := 0x300201000
noncomputable def e125d_right : Nat → Nat
  | 0 => e125d_right_0
  | _ => 0
noncomputable def e125d_scale : Nat := 0x1c000000000002d01000
noncomputable def e125d_target0 : Nat := 0x7db32923fc0077b1b2500000c317a80000000dd000000000bc000000000003005000
noncomputable def e125d_target1 : Nat := 0x30000000002201000
noncomputable def e125d_target2 : Nat := 0x300201000
noncomputable def e125d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 150
  maxLength := 5
  maxWidth := 48
  terms := 1
  left := e125d_left
  right := e125d_right
  scale := e125d_scale
  target0 := e125d_target0
  target1 := e125d_target1
  target2 := e125d_target2

theorem e125d_ok : e125d.check=true := by decide +kernel
noncomputable def e126n_left_0 : Nat := 0x8018a7e654e0900cecc0002b00000001e04000
noncomputable def e126n_left : Nat → Nat
  | 0 => e126n_left_0
  | _ => 0
noncomputable def e126n_right_0 : Nat := 0x300201000
noncomputable def e126n_right : Nat → Nat
  | 0 => e126n_right_0
  | _ => 0
noncomputable def e126n_scale : Nat := 0x70000000002301000
noncomputable def e126n_target0 : Nat := 0x8018a7e40254e090000cecc000002b0000000002604000
noncomputable def e126n_target1 : Nat := 0x700000001b01000
noncomputable def e126n_target2 : Nat := 0x300201000
noncomputable def e126n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 120
  maxLength := 4
  maxWidth := 38
  terms := 1
  left := e126n_left
  right := e126n_right
  scale := e126n_scale
  target0 := e126n_target0
  target1 := e126n_target1
  target2 := e126n_target2

theorem e126n_ok : e126n.check=true := by decide +kernel
noncomputable def e126d_left_0 : Nat := 0x54f0000a02000
noncomputable def e126d_left : Nat → Nat
  | 0 => e126d_left_0
  | _ => 0
noncomputable def e126d_right_0 : Nat := 0x300201000
noncomputable def e126d_right : Nat → Nat
  | 0 => e126d_right_0
  | _ => 0
noncomputable def e126d_scale : Nat := 0x7000001301000
noncomputable def e126d_target0 : Nat := 0xfc807000001302000
noncomputable def e126d_target1 : Nat := 0x30000a01000
noncomputable def e126d_target2 : Nat := 0x300201000
noncomputable def e126d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 60
  maxLength := 2
  maxWidth := 19
  terms := 1
  left := e126d_left
  right := e126d_right
  scale := e126d_scale
  target0 := e126d_target0
  target1 := e126d_target1
  target2 := e126d_target2

theorem e126d_ok : e126d.check=true := by decide +kernel
noncomputable def e127n_left_0 : Nat := 0x7ffb583b32e61802583a1ee700845f9f33a0000a072e9e000000c6a9500000000a4b000000000003406000
noncomputable def e127n_left : Nat → Nat
  | 0 => e127n_left_0
  | _ => 0
noncomputable def e127n_right_0 : Nat := 0x300201000
noncomputable def e127n_right : Nat → Nat
  | 0 => e127n_right_0
  | _ => 0
noncomputable def e127n_scale : Nat := 0x3400000000000003601000
noncomputable def e127n_target0 : Nat := 0x7ffb583b32e6100802583a1ee70000845f9f33a000000a072e9e00000000c6a950000000000a4b00000000000003c06000
noncomputable def e127n_target1 : Nat := 0x34000000000002e01000
noncomputable def e127n_target2 : Nat := 0x300201000
noncomputable def e127n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 187
  maxLength := 6
  maxWidth := 60
  terms := 1
  left := e127n_left
  right := e127n_right
  scale := e127n_scale
  target0 := e127n_target0
  target1 := e127n_target1
  target2 := e127n_target2

theorem e127n_ok : e127n.check=true := by decide +kernel
noncomputable def e127d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e127d_left : Nat → Nat
  | 0 => e127d_left_0
  | _ => 0
noncomputable def e127d_right_0 : Nat := 0x300201000
noncomputable def e127d_right : Nat → Nat
  | 0 => e127d_right_0
  | _ => 0
noncomputable def e127d_scale : Nat := 0xc00000000000003401000
noncomputable def e127d_target0 : Nat := 0x7f01731e38f001e55eca6a4000091edd260000002a06080000000001b00000000003400000000000003606000
noncomputable def e127d_target1 : Nat := 0x3000000000002a01000
noncomputable def e127d_target2 : Nat := 0x300201000
noncomputable def e127d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 169
  maxLength := 6
  maxWidth := 54
  terms := 1
  left := e127d_left
  right := e127d_right
  scale := e127d_scale
  target0 := e127d_target0
  target1 := e127d_target1
  target2 := e127d_target2

theorem e127d_ok : e127d.check=true := by decide +kernel
noncomputable def e128n_left_0 : Nat := 0x10002512f2e35fee007d4c74eb6b003f306b1686d000067401b6a800000075e1194000000011cbb000000000039300000000000003b07000
noncomputable def e128n_left : Nat → Nat
  | 0 => e128n_left_0
  | _ => 0
noncomputable def e128n_right_0 : Nat := 0x300201000
noncomputable def e128n_right : Nat → Nat
  | 0 => e128n_right_0
  | _ => 0
noncomputable def e128n_scale : Nat := 0x340000000000000003e01000
noncomputable def e128n_target0 : Nat := 0x80012897971aff600801f531d3adac00007e60d62d0da00000067401b6a8000000003af08ca0000000000472ec0000000000007260000000000000004407000
noncomputable def e128n_target1 : Nat := 0x1a00000000000003501000
noncomputable def e128n_target2 : Nat := 0x300201000
noncomputable def e128n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 212
  maxLength := 7
  maxWidth := 68
  terms := 1
  left := e128n_left
  right := e128n_right
  scale := e128n_scale
  target0 := e128n_target0
  target1 := e128n_target1
  target2 := e128n_target2

theorem e128n_ok : e128n.check=true := by decide +kernel
noncomputable def e128d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e128d_left : Nat → Nat
  | 0 => e128d_left_0
  | _ => 0
noncomputable def e128d_right_0 : Nat := 0x300201000
noncomputable def e128d_right : Nat → Nat
  | 0 => e128d_right_0
  | _ => 0
noncomputable def e128d_scale : Nat := 0xc00000000000003401000
noncomputable def e128d_target0 : Nat := 0x7f01731e38f001e55eca6a4000091edd260000002a06080000000001b00000000003400000000000003606000
noncomputable def e128d_target1 : Nat := 0x3000000000002a01000
noncomputable def e128d_target2 : Nat := 0x300201000
noncomputable def e128d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 169
  maxLength := 6
  maxWidth := 54
  terms := 1
  left := e128d_left
  right := e128d_right
  scale := e128d_scale
  target0 := e128d_target0
  target1 := e128d_target1
  target2 := e128d_target2

theorem e128d_ok : e128d.check=true := by decide +kernel
noncomputable def e129n_left_0 : Nat := 0x800435da33a25b80098b0690c6007c63c21f5d00005ecc2ab40000003595a5000000005d2600000000008300000000000003807000
noncomputable def e129n_left : Nat → Nat
  | 0 => e129n_left_0
  | _ => 0
noncomputable def e129n_right_0 : Nat := 0x300201000
noncomputable def e129n_right : Nat → Nat
  | 0 => e129n_right_0
  | _ => 0
noncomputable def e129n_scale : Nat := 0x340000000000000003e01000
noncomputable def e129n_target0 : Nat := 0x800435da33a25b00080098b0690c6000007c63c21f5d00000005ecc2ab40000000003595a5000000000005d2600000000000008300000000000000004407000
noncomputable def e129n_target1 : Nat := 0x340000000000003201000
noncomputable def e129n_target2 : Nat := 0x300201000
noncomputable def e129n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 212
  maxLength := 7
  maxWidth := 68
  terms := 1
  left := e129n_left
  right := e129n_right
  scale := e129n_scale
  target0 := e129n_target0
  target1 := e129n_target1
  target2 := e129n_target2

theorem e129n_ok : e129n.check=true := by decide +kernel
noncomputable def e129d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e129d_left : Nat → Nat
  | 0 => e129d_left_0
  | _ => 0
noncomputable def e129d_right_0 : Nat := 0x300201000
noncomputable def e129d_right : Nat → Nat
  | 0 => e129d_right_0
  | _ => 0
noncomputable def e129d_scale : Nat := 0xc00000000000003401000
noncomputable def e129d_target0 : Nat := 0x7f01731e38f001e55eca6a4000091edd260000002a06080000000001b00000000003400000000000003606000
noncomputable def e129d_target1 : Nat := 0x3000000000002a01000
noncomputable def e129d_target2 : Nat := 0x300201000
noncomputable def e129d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 169
  maxLength := 6
  maxWidth := 54
  terms := 1
  left := e129d_left
  right := e129d_right
  scale := e129d_scale
  target0 := e129d_target0
  target1 := e129d_target1
  target2 := e129d_target2

theorem e129d_ok : e129d.check=true := by decide +kernel
end ThomsonNegative.Certificate.Bridges.RFChecks
