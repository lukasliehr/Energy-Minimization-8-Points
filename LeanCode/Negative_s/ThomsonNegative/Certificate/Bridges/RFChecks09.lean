import ThomsonNegative.Structure.Packed.IdentityKernel
namespace ThomsonNegative.Certificate.Bridges.RFChecks
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
noncomputable def e90n_left_0 : Nat := 0x1ffea6c2922806ab7fd51d9babf2d801fe975f481bd000078f28fd650000000d3e76b500000000072d58000000000134300000000000003e07000
noncomputable def e90n_left : Nat → Nat
  | 0 => e90n_left_0
  | _ => 0
noncomputable def e90n_right_0 : Nat := 0x300201000
noncomputable def e90n_right : Nat → Nat
  | 0 => e90n_right_0
  | _ => 0
noncomputable def e90n_scale : Nat := 0x3680000000000000004201000
noncomputable def e90n_target0 : Nat := 0x1ffea6c2922806ab007fd51d9babf2d80001fe975f481bd00000078f28fd65000000000d3e76b50000000000072d580000000000013430000000000000004607000
noncomputable def e90n_target1 : Nat := 0x36800000000000003a01000
noncomputable def e90n_target2 : Nat := 0x300201000
noncomputable def e90n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 218
  maxLength := 7
  maxWidth := 70
  terms := 1
  left := e90n_left
  right := e90n_right
  scale := e90n_scale
  target0 := e90n_target0
  target1 := e90n_target1
  target2 := e90n_target2

theorem e90n_ok : e90n.check=true := by decide +kernel
noncomputable def e90d_left_0 : Nat := 0xfceee18557a7676e00565d380000cf800000150000000002505000
noncomputable def e90d_left : Nat → Nat
  | 0 => e90d_left_0
  | _ => 0
noncomputable def e90d_right_0 : Nat := 0x300201000
noncomputable def e90d_right : Nat → Nat
  | 0 => e90d_right_0
  | _ => 0
noncomputable def e90d_scale : Nat := 0xc8000000000003001000
noncomputable def e90d_target0 : Nat := 0x3f232f6d7e80079c545bc0000164a37c0000000a97000000000568000000000003305000
noncomputable def e90d_target1 : Nat := 0x30000000002201000
noncomputable def e90d_target2 : Nat := 0x300201000
noncomputable def e90d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 159
  maxLength := 5
  maxWidth := 51
  terms := 1
  left := e90d_left
  right := e90d_right
  scale := e90d_scale
  target0 := e90d_target0
  target1 := e90d_target1
  target2 := e90d_target2

theorem e90d_ok : e90d.check=true := by decide +kernel
noncomputable def e91n_left_0 : Nat := 0x800182097ced8b200c016a64446c629f40201eb883c3c69a000102bb00b6349000000b8281cb79800000007eeb041c0000000003660fe0000000000012730000000000000004508000
noncomputable def e91n_left : Nat → Nat
  | 0 => e91n_left_0
  | _ => 0
noncomputable def e91n_right_0 : Nat := 0x300201000
noncomputable def e91n_right : Nat → Nat
  | 0 => e91n_right_0
  | _ => 0
noncomputable def e91n_scale : Nat := 0x368000000000000000004a01000
noncomputable def e91n_target0 : Nat := 0x800182097ced8b20080200b5322236314fa0000807ae20f0f1a680000020576016c69200000000b8281cb7980000000003f75820e000000000000d983f8000000000000024e6000000000000000004e08000
noncomputable def e91n_target1 : Nat := 0x1b40000000000000004101000
noncomputable def e91n_target2 : Nat := 0x300201000
noncomputable def e91n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 243
  maxLength := 8
  maxWidth := 78
  terms := 1
  left := e91n_left
  right := e91n_right
  scale := e91n_scale
  target0 := e91n_target0
  target1 := e91n_target1
  target2 := e91n_target2

theorem e91n_ok : e91n.check=true := by decide +kernel
noncomputable def e91d_left_0 : Nat := 0xfceee18557a7676e00565d380000cf800000150000000002505000
noncomputable def e91d_left : Nat → Nat
  | 0 => e91d_left_0
  | _ => 0
noncomputable def e91d_right_0 : Nat := 0x300201000
noncomputable def e91d_right : Nat → Nat
  | 0 => e91d_right_0
  | _ => 0
noncomputable def e91d_scale : Nat := 0xc8000000000003001000
noncomputable def e91d_target0 : Nat := 0x3f232f6d7e80079c545bc0000164a37c0000000a97000000000568000000000003305000
noncomputable def e91d_target1 : Nat := 0x30000000002201000
noncomputable def e91d_target2 : Nat := 0x300201000
noncomputable def e91d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 159
  maxLength := 5
  maxWidth := 51
  terms := 1
  left := e91d_left
  right := e91d_right
  scale := e91d_scale
  target0 := e91d_target0
  target1 := e91d_target1
  target2 := e91d_target2

theorem e91d_ok : e91d.check=true := by decide +kernel
noncomputable def e92n_left_0 : Nat := 0x8001475904782ba55c00baeb5d2bea0fc02001b290a7e3de000101931e39503000000a9e9b70a88000000060e503b400000000024f4aa000000000000f910000000000000004508000
noncomputable def e92n_left : Nat → Nat
  | 0 => e92n_left_0
  | _ => 0
noncomputable def e92n_right_0 : Nat := 0x300201000
noncomputable def e92n_right : Nat → Nat
  | 0 => e92n_right_0
  | _ => 0
noncomputable def e92n_scale : Nat := 0x368000000000000000004a01000
noncomputable def e92n_target0 : Nat := 0x8001475904782ba55801002ebad74afa83f00002001b290a7e3de0000004064c78e540c00000000a9e9b70a88000000000183940ed00000000000024f4aa000000000000003e44000000000000000004f08000
noncomputable def e92n_target1 : Nat := 0xda0000000000000004001000
noncomputable def e92n_target2 : Nat := 0x300201000
noncomputable def e92n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 246
  maxLength := 8
  maxWidth := 79
  terms := 1
  left := e92n_left
  right := e92n_right
  scale := e92n_scale
  target0 := e92n_target0
  target1 := e92n_target1
  target2 := e92n_target2

theorem e92n_ok : e92n.check=true := by decide +kernel
noncomputable def e92d_left_0 : Nat := 0xfceee18557a7676e00565d380000cf800000150000000002505000
noncomputable def e92d_left : Nat → Nat
  | 0 => e92d_left_0
  | _ => 0
noncomputable def e92d_right_0 : Nat := 0x300201000
noncomputable def e92d_right : Nat → Nat
  | 0 => e92d_right_0
  | _ => 0
noncomputable def e92d_scale : Nat := 0xc8000000000003001000
noncomputable def e92d_target0 : Nat := 0x3f232f6d7e80079c545bc0000164a37c0000000a97000000000568000000000003305000
noncomputable def e92d_target1 : Nat := 0x30000000002201000
noncomputable def e92d_target2 : Nat := 0x300201000
noncomputable def e92d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 159
  maxLength := 5
  maxWidth := 51
  terms := 1
  left := e92d_left
  right := e92d_right
  scale := e92d_scale
  target0 := e92d_target0
  target1 := e92d_target1
  target2 := e92d_target2

theorem e92d_ok : e92d.check=true := by decide +kernel
noncomputable def e93n_left_0 : Nat := 0x3f697d05017fb982d8005e50580000346000000310000000002705000
noncomputable def e93n_left : Nat → Nat
  | 0 => e93n_left_0
  | _ => 0
noncomputable def e93n_right_0 : Nat := 0x300201000
noncomputable def e93n_right : Nat → Nat
  | 0 => e93n_right_0
  | _ => 0
noncomputable def e93n_scale : Nat := 0x19000000000002d01000
noncomputable def e93n_target0 : Nat := 0x3f697d0501007fb982d800005e50580000003460000000031000000000002f05000
noncomputable def e93n_target1 : Nat := 0x190000000002501000
noncomputable def e93n_target2 : Nat := 0x300201000
noncomputable def e93n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 147
  maxLength := 5
  maxWidth := 47
  terms := 1
  left := e93n_left
  right := e93n_right
  scale := e93n_scale
  target0 := e93n_target0
  target1 := e93n_target1
  target2 := e93n_target2

theorem e93n_ok : e93n.check=true := by decide +kernel
noncomputable def e93d_left_0 : Nat := 0x54f0000a02000
noncomputable def e93d_left : Nat → Nat
  | 0 => e93d_left_0
  | _ => 0
noncomputable def e93d_right_0 : Nat := 0x300201000
noncomputable def e93d_right : Nat → Nat
  | 0 => e93d_right_0
  | _ => 0
noncomputable def e93d_scale : Nat := 0x19000001501000
noncomputable def e93d_target0 : Nat := 0x13d6019000001502000
noncomputable def e93d_target1 : Nat := 0x30000a01000
noncomputable def e93d_target2 : Nat := 0x300201000
noncomputable def e93d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 66
  maxLength := 2
  maxWidth := 21
  terms := 1
  left := e93d_left
  right := e93d_right
  scale := e93d_scale
  target0 := e93d_target0
  target1 := e93d_target1
  target2 := e93d_target2

theorem e93d_ok : e93d.check=true := by decide +kernel
noncomputable def e94n_left_0 : Nat := 0x800d3d76e2a7f80d4fa75fb900845c41d86000088daea20000006d1cb000000003d5000000000003406000
noncomputable def e94n_left : Nat → Nat
  | 0 => e94n_left_0
  | _ => 0
noncomputable def e94n_right_0 : Nat := 0x300201000
noncomputable def e94n_right : Nat → Nat
  | 0 => e94n_right_0
  | _ => 0
noncomputable def e94n_scale : Nat := 0xf800000000000003801000
noncomputable def e94n_target0 : Nat := 0x20034f5db8a9fc0101a9f4ebf720000845c41d86000000446d751000000001b472c00000000007aa00000000000003d06000
noncomputable def e94n_target1 : Nat := 0x7c000000000002f01000
noncomputable def e94n_target2 : Nat := 0x300201000
noncomputable def e94n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 190
  maxLength := 6
  maxWidth := 61
  terms := 1
  left := e94n_left
  right := e94n_right
  scale := e94n_scale
  target0 := e94n_target0
  target1 := e94n_target1
  target2 := e94n_target2

theorem e94n_ok : e94n.check=true := by decide +kernel
noncomputable def e94d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e94d_left : Nat → Nat
  | 0 => e94d_left_0
  | _ => 0
noncomputable def e94d_right_0 : Nat := 0x300201000
noncomputable def e94d_right : Nat → Nat
  | 0 => e94d_right_0
  | _ => 0
noncomputable def e94d_scale : Nat := 0x3800000000000003601000
noncomputable def e94d_target0 : Nat := 0x1fd04595aaad000f6038be7d800008d725dc80000004f090c000000000851000000000017800000000000003906000
noncomputable def e94d_target1 : Nat := 0x3000000000002a01000
noncomputable def e94d_target2 : Nat := 0x300201000
noncomputable def e94d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 178
  maxLength := 6
  maxWidth := 57
  terms := 1
  left := e94d_left
  right := e94d_right
  scale := e94d_scale
  target0 := e94d_target0
  target1 := e94d_target1
  target2 := e94d_target2

theorem e94d_ok : e94d.check=true := by decide +kernel
noncomputable def e95n_left_0 : Nat := 0xffff0e7ac84e7dfe0f097366f003c8a54b4690000684ff4880000012a030400000003fff00000000005700000000000003707000
noncomputable def e95n_left : Nat → Nat
  | 0 => e95n_left_0
  | _ => 0
noncomputable def e95n_right_0 : Nat := 0x300201000
noncomputable def e95n_right : Nat → Nat
  | 0 => e95n_right_0
  | _ => 0
noncomputable def e95n_scale : Nat := 0xf80000000000000004001000
noncomputable def e95n_target0 : Nat := 0x7fff873d64273e0007f83c25cd9bc000007914a968d20000000684ff48800000000095018200000000000fffc0000000000000ae00000000000000004407000
noncomputable def e95n_target1 : Nat := 0x7c0000000000003301000
noncomputable def e95n_target2 : Nat := 0x300201000
noncomputable def e95n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 212
  maxLength := 7
  maxWidth := 68
  terms := 1
  left := e95n_left
  right := e95n_right
  scale := e95n_scale
  target0 := e95n_target0
  target1 := e95n_target1
  target2 := e95n_target2

theorem e95n_ok : e95n.check=true := by decide +kernel
noncomputable def e95d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e95d_left : Nat → Nat
  | 0 => e95d_left_0
  | _ => 0
noncomputable def e95d_right_0 : Nat := 0x300201000
noncomputable def e95d_right : Nat → Nat
  | 0 => e95d_right_0
  | _ => 0
noncomputable def e95d_scale : Nat := 0x3800000000000003601000
noncomputable def e95d_target0 : Nat := 0x1fd04595aaad000f6038be7d800008d725dc80000004f090c000000000851000000000017800000000000003906000
noncomputable def e95d_target1 : Nat := 0x3000000000002a01000
noncomputable def e95d_target2 : Nat := 0x300201000
noncomputable def e95d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 178
  maxLength := 6
  maxWidth := 57
  terms := 1
  left := e95d_left
  right := e95d_right
  scale := e95d_scale
  target0 := e95d_target0
  target1 := e95d_target1
  target2 := e95d_target2

theorem e95d_ok : e95d.check=true := by decide +kernel
noncomputable def e96n_left_0 : Nat := 0x1fff2244d88c7fd7f7f6d511856801eccecabe9b0000741f41d3000000259c02300000000c82e80000000001e500000000000003a07000
noncomputable def e96n_left : Nat → Nat
  | 0 => e96n_left_0
  | _ => 0
noncomputable def e96n_right_0 : Nat := 0x300201000
noncomputable def e96n_right : Nat → Nat
  | 0 => e96n_right_0
  | _ => 0
noncomputable def e96n_scale : Nat := 0xf80000000000000004001000
noncomputable def e96n_target0 : Nat := 0x3ffe4489b118ffa001fdfdb544615a00000f667655f4d8000000741f41d30000000004b380460000000000320ba0000000000000f280000000000000004507000
noncomputable def e96n_target1 : Nat := 0x1f00000000000003501000
noncomputable def e96n_target2 : Nat := 0x300201000
noncomputable def e96n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 215
  maxLength := 7
  maxWidth := 69
  terms := 1
  left := e96n_left
  right := e96n_right
  scale := e96n_scale
  target0 := e96n_target0
  target1 := e96n_target1
  target2 := e96n_target2

theorem e96n_ok : e96n.check=true := by decide +kernel
noncomputable def e96d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e96d_left : Nat → Nat
  | 0 => e96d_left_0
  | _ => 0
noncomputable def e96d_right_0 : Nat := 0x300201000
noncomputable def e96d_right : Nat → Nat
  | 0 => e96d_right_0
  | _ => 0
noncomputable def e96d_scale : Nat := 0x3800000000000003601000
noncomputable def e96d_target0 : Nat := 0x1fd04595aaad000f6038be7d800008d725dc80000004f090c000000000851000000000017800000000000003906000
noncomputable def e96d_target1 : Nat := 0x3000000000002a01000
noncomputable def e96d_target2 : Nat := 0x300201000
noncomputable def e96d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 178
  maxLength := 6
  maxWidth := 57
  terms := 1
  left := e96d_left
  right := e96d_right
  scale := e96d_scale
  target0 := e96d_target0
  target1 := e96d_target1
  target2 := e96d_target2

theorem e96d_ok : e96d.check=true := by decide +kernel
noncomputable def e97n_left_0 : Nat := 0x7fff444c871a9daa02ffed4e90150079f401ffd247364872680003feb640b3d490000007ae554fbe600000000e4bd441c0000000002646bf80000000000064730000000000000004708000
noncomputable def e97n_left : Nat → Nat
  | 0 => e97n_left_0
  | _ => 0
noncomputable def e97n_right_0 : Nat := 0x300201000
noncomputable def e97n_right : Nat → Nat
  | 0 => e97n_right_0
  | _ => 0
noncomputable def e97n_scale : Nat := 0x1f0000000000000000004901000
noncomputable def e97n_target0 : Nat := 0x7fff444c871a9daa02007ff6a7480a803cfa00007ff491cd921c9a0000007fd6c8167a92000000007ae554fbe60000000000725ea20e000000000000991afe00000000000000c8e6000000000000000005008000
noncomputable def e97n_target1 : Nat := 0xf80000000000000004001000
noncomputable def e97n_target2 : Nat := 0x300201000
noncomputable def e97n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 249
  maxLength := 8
  maxWidth := 80
  terms := 1
  left := e97n_left
  right := e97n_right
  scale := e97n_scale
  target0 := e97n_target0
  target1 := e97n_target1
  target2 := e97n_target2

theorem e97n_ok : e97n.check=true := by decide +kernel
noncomputable def e97d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e97d_left : Nat → Nat
  | 0 => e97d_left_0
  | _ => 0
noncomputable def e97d_right_0 : Nat := 0x300201000
noncomputable def e97d_right : Nat → Nat
  | 0 => e97d_right_0
  | _ => 0
noncomputable def e97d_scale : Nat := 0x7000000000000003701000
noncomputable def e97d_target0 : Nat := 0x7f411656aab4001ec0717cfb000008d725dc8000000278486000000000214400000000002f000000000000003a06000
noncomputable def e97d_target1 : Nat := 0x3000000000002a01000
noncomputable def e97d_target2 : Nat := 0x300201000
noncomputable def e97d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 181
  maxLength := 6
  maxWidth := 58
  terms := 1
  left := e97d_left
  right := e97d_right
  scale := e97d_scale
  target0 := e97d_target0
  target1 := e97d_target1
  target2 := e97d_target2

theorem e97d_ok : e97d.check=true := by decide +kernel
noncomputable def e98n_left_0 : Nat := 0x80044d5088c507df014c81d296a94c021be5067e69180004adb48be870000006a1faeba000000000f17a400000000014688000000000003d0000000000000003f08000
noncomputable def e98n_left : Nat → Nat
  | 0 => e98n_left_0
  | _ => 0
noncomputable def e98n_right_0 : Nat := 0x300201000
noncomputable def e98n_right : Nat → Nat
  | 0 => e98n_right_0
  | _ => 0
noncomputable def e98n_scale : Nat := 0xf8000000000000000004801000
noncomputable def e98n_target0 : Nat := 0x80044d5088c507de00080a640e94b54a60000086f9419f9a46000000095b6917d0e0000000006a1faeba00000000000078bd2000000000000051a20000000000000007a0000000000000000004c08000
noncomputable def e98n_target1 : Nat := 0x7c000000000000003b01000
noncomputable def e98n_target2 : Nat := 0x300201000
noncomputable def e98n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 237
  maxLength := 8
  maxWidth := 76
  terms := 1
  left := e98n_left
  right := e98n_right
  scale := e98n_scale
  target0 := e98n_target0
  target1 := e98n_target1
  target2 := e98n_target2

theorem e98n_ok : e98n.check=true := by decide +kernel
noncomputable def e98d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e98d_left : Nat → Nat
  | 0 => e98d_left_0
  | _ => 0
noncomputable def e98d_right_0 : Nat := 0x300201000
noncomputable def e98d_right : Nat → Nat
  | 0 => e98d_right_0
  | _ => 0
noncomputable def e98d_scale : Nat := 0x3800000000000003601000
noncomputable def e98d_target0 : Nat := 0x1fd04595aaad000f6038be7d800008d725dc80000004f090c000000000851000000000017800000000000003906000
noncomputable def e98d_target1 : Nat := 0x3000000000002a01000
noncomputable def e98d_target2 : Nat := 0x300201000
noncomputable def e98d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 178
  maxLength := 6
  maxWidth := 57
  terms := 1
  left := e98d_left
  right := e98d_right
  scale := e98d_scale
  target0 := e98d_target0
  target1 := e98d_target1
  target2 := e98d_target2

theorem e98d_ok : e98d.check=true := by decide +kernel
noncomputable def e99n_left_0 : Nat := 0x8002464b07454d28300a2dc899e5a4f4020f7ab08b92468000477bdbe00090000007262d7166000000004889d1c0000000001f41f8000000000004b30000000000000004308000
noncomputable def e99n_left : Nat → Nat
  | 0 => e99n_left_0
  | _ => 0
noncomputable def e99n_right_0 : Nat := 0x300201000
noncomputable def e99n_right : Nat → Nat
  | 0 => e99n_right_0
  | _ => 0
noncomputable def e99n_scale : Nat := 0xf8000000000000000004801000
noncomputable def e99n_target0 : Nat := 0x8002464b07454d282004028b722679693d000020f7ab08b924680000011def6f80024000000007262d7166000000000012227470000000000001f41f8000000000000012cc000000000000000004d08000
noncomputable def e99n_target1 : Nat := 0x3e0000000000000003e01000
noncomputable def e99n_target2 : Nat := 0x300201000
noncomputable def e99n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 240
  maxLength := 8
  maxWidth := 77
  terms := 1
  left := e99n_left
  right := e99n_right
  scale := e99n_scale
  target0 := e99n_target0
  target1 := e99n_target1
  target2 := e99n_target2

theorem e99n_ok : e99n.check=true := by decide +kernel
noncomputable def e99d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e99d_left : Nat → Nat
  | 0 => e99d_left_0
  | _ => 0
noncomputable def e99d_right_0 : Nat := 0x300201000
noncomputable def e99d_right : Nat → Nat
  | 0 => e99d_right_0
  | _ => 0
noncomputable def e99d_scale : Nat := 0x3800000000000003601000
noncomputable def e99d_target0 : Nat := 0x1fd04595aaad000f6038be7d800008d725dc80000004f090c000000000851000000000017800000000000003906000
noncomputable def e99d_target1 : Nat := 0x3000000000002a01000
noncomputable def e99d_target2 : Nat := 0x300201000
noncomputable def e99d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 178
  maxLength := 6
  maxWidth := 57
  terms := 1
  left := e99d_left
  right := e99d_right
  scale := e99d_scale
  target0 := e99d_target0
  target1 := e99d_target1
  target2 := e99d_target2

theorem e99d_ok : e99d.check=true := by decide +kernel
end ThomsonNegative.Certificate.Bridges.RFChecks
