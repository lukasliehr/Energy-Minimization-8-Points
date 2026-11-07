import ThomsonNegative.Structure.Packed.IdentityKernel
namespace ThomsonNegative.Certificate.Bridges.RFChecks
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
noncomputable def e30n_left_0 : Nat := 0x7fffc17c563f12980ad8001e2876e362f81800801fa668f91efac00008021fed1f262800000082bd044d18e00000000a864471a80000000000d5d0c2c000000000000921980000000000000086d000000000000000004c09000
noncomputable def e30n_left : Nat → Nat
  | 0 => e30n_left_0
  | _ => 0
noncomputable def e30n_right_0 : Nat := 0x300201000
noncomputable def e30n_right : Nat → Nat
  | 0 => e30n_right_0
  | _ => 0
noncomputable def e30n_scale : Nat := 0x79800000000000000000005301000
noncomputable def e30n_target0 : Nat := 0x3fffe0be2b1f894c0568008001e2876e362f81800001003f4cd1f23df5800000020087fb47c98a000000000415e82268c700000000000a864471a80000000000001aba1858000000000000002486600000000000000000436800000000000000000005709000
noncomputable def e30n_target1 : Nat := 0xf3000000000000000004801000
noncomputable def e30n_target2 : Nat := 0x300201000
noncomputable def e30n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 270
  maxLength := 9
  maxWidth := 87
  terms := 1
  left := e30n_left
  right := e30n_right
  scale := e30n_scale
  target0 := e30n_target0
  target1 := e30n_target1
  target2 := e30n_target2

theorem e30n_ok : e30n.check=true := by decide +kernel
noncomputable def e30d_left_0 : Nat := 0x7ff3943c72685b806c506d541600891ac7608d00008ecf3ed4000000488f050000000044b60000000000f300000000000003807000
noncomputable def e30d_left : Nat → Nat
  | 0 => e30d_left_0
  | _ => 0
noncomputable def e30d_right_0 : Nat := 0x300201000
noncomputable def e30d_right : Nat → Nat
  | 0 => e30d_right_0
  | _ => 0
noncomputable def e30d_scale : Nat := 0x180000000000000003d01000
noncomputable def e30d_target0 : Nat := 0xffe72878e4d0b600201b141b550580000448d63b04680000008ecf3ed4000000000911e0a0000000000112d80000000000007980000000000000004307000
noncomputable def e30d_target1 : Nat := 0x300000000000003201000
noncomputable def e30d_target2 : Nat := 0x300201000
noncomputable def e30d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 209
  maxLength := 7
  maxWidth := 67
  terms := 1
  left := e30d_left
  right := e30d_right
  scale := e30d_scale
  target0 := e30d_target0
  target1 := e30d_target1
  target2 := e30d_target2

theorem e30d_ok : e30d.check=true := by decide +kernel
noncomputable def e31n_left_0 : Nat := 0x7ffff67ad7bfc7f78e28ba60001f1ecef39ed5155eb008002a6df5d45063a09000020067ef578f6d77dc00000080677ad4a82673800000001fdce8d94173a000000000080e171e1c50000000000002b2b07e0c00000000000000df9fc44000000000000000271f300000000000000000005a0a000
noncomputable def e31n_left : Nat → Nat
  | 0 => e31n_left_0
  | _ => 0
noncomputable def e31n_right_0 : Nat := 0x300201000
noncomputable def e31n_right : Nat → Nat
  | 0 => e31n_right_0
  | _ => 0
noncomputable def e31n_scale : Nat := 0xf300000000000000000000005c01000
noncomputable def e31n_target0 : Nat := 0x7ffff67ad7bfc7f78e28ba4020001f1ecef39ed5155eb00008002a6df5d45063a0900000020067ef578f6d77dc0000000080677ad4a8267380000000001fdce8d94173a00000000000080e171e1c5000000000000002b2b07e0c0000000000000000df9fc4400000000000000000271f3000000000000000000000620a000
noncomputable def e31n_target1 : Nat := 0xf3000000000000000000005401000
noncomputable def e31n_target2 : Nat := 0x300201000
noncomputable def e31n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 303
  maxLength := 10
  maxWidth := 98
  terms := 1
  left := e31n_left
  right := e31n_right
  scale := e31n_scale
  target0 := e31n_target0
  target1 := e31n_target1
  target2 := e31n_target2

theorem e31n_ok : e31n.check=true := by decide +kernel
noncomputable def e31d_left_0 : Nat := 0x7ff3943c72685b806c506d541600891ac7608d00008ecf3ed4000000488f050000000044b60000000000f300000000000003807000
noncomputable def e31d_left : Nat → Nat
  | 0 => e31d_left_0
  | _ => 0
noncomputable def e31d_right_0 : Nat := 0x300201000
noncomputable def e31d_right : Nat → Nat
  | 0 => e31d_right_0
  | _ => 0
noncomputable def e31d_scale : Nat := 0x300000000000000003e01000
noncomputable def e31d_target0 : Nat := 0x7ff3943c72685b000806c506d541600000891ac7608d00000008ecf3ed4000000000488f050000000000044b60000000000000f300000000000000004407000
noncomputable def e31d_target1 : Nat := 0x300000000000003201000
noncomputable def e31d_target2 : Nat := 0x300201000
noncomputable def e31d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 212
  maxLength := 7
  maxWidth := 68
  terms := 1
  left := e31d_left
  right := e31d_right
  scale := e31d_scale
  target0 := e31d_target0
  target1 := e31d_target1
  target2 := e31d_target2

theorem e31d_ok : e31d.check=true := by decide +kernel
noncomputable def e32n_left_0 : Nat := 0x1ffffdfd060ccfda60423c0001d6f9a48ea2ea8500800080a70953243380001005456348268f90000001fccde60efc690000000030c8597f5e600000000002de458b580000000000009e81ad000000000000001c64f80000000000000003fd0000000000000000000530a000
noncomputable def e32n_left : Nat → Nat
  | 0 => e32n_left_0
  | _ => 0
noncomputable def e32n_right_0 : Nat := 0x300201000
noncomputable def e32n_right : Nat → Nat
  | 0 => e32n_right_0
  | _ => 0
noncomputable def e32n_scale : Nat := 0x7980000000000000000000005b01000
noncomputable def e32n_target0 : Nat := 0x1ffffdfd060ccfda6042380040001d6f9a48ea2ea8500000800080a70953243380000001005456348268f90000000001fccde60efc690000000000030c8597f5e600000000000002de458b580000000000000009e81ad000000000000000001c64f80000000000000000003fd00000000000000000000005f0a000
noncomputable def e32n_target1 : Nat := 0x7980000000000000000004f01000
noncomputable def e32n_target2 : Nat := 0x300201000
noncomputable def e32n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 294
  maxLength := 10
  maxWidth := 95
  terms := 1
  left := e32n_left
  right := e32n_right
  scale := e32n_scale
  target0 := e32n_target0
  target1 := e32n_target1
  target2 := e32n_target2

theorem e32n_ok : e32n.check=true := by decide +kernel
noncomputable def e32d_left_0 : Nat := 0x7ff3943c72685b806c506d541600891ac7608d00008ecf3ed4000000488f050000000044b60000000000f300000000000003807000
noncomputable def e32d_left : Nat → Nat
  | 0 => e32d_left_0
  | _ => 0
noncomputable def e32d_right_0 : Nat := 0x300201000
noncomputable def e32d_right : Nat → Nat
  | 0 => e32d_right_0
  | _ => 0
noncomputable def e32d_scale : Nat := 0x180000000000000003d01000
noncomputable def e32d_target0 : Nat := 0xffe72878e4d0b600201b141b550580000448d63b04680000008ecf3ed4000000000911e0a0000000000112d80000000000007980000000000000004307000
noncomputable def e32d_target1 : Nat := 0x300000000000003201000
noncomputable def e32d_target2 : Nat := 0x300201000
noncomputable def e32d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 209
  maxLength := 7
  maxWidth := 67
  terms := 1
  left := e32d_left
  right := e32d_right
  scale := e32d_scale
  target0 := e32d_target0
  target1 := e32d_target1
  target2 := e32d_target2

theorem e32d_ok : e32d.check=true := by decide +kernel
noncomputable def e33n_left_0 : Nat := 0x2000025bdcf8eb43c54cefffe75fab10a8d2185007ff88ab47988e68e0000401d5ddbab69390000001f957cc619b2400000000af2d4236e6000000000021a7589600000000000035df6d0000000000000021d7e0000000000000000fd0000000000000000000510a000
noncomputable def e33n_left : Nat → Nat
  | 0 => e33n_left_0
  | _ => 0
noncomputable def e33n_right_0 : Nat := 0x300201000
noncomputable def e33n_right : Nat → Nat
  | 0 => e33n_right_0
  | _ => 0
noncomputable def e33n_scale : Nat := 0x7980000000000000000000005b01000
noncomputable def e33n_target0 : Nat := 0x2000025bdcf8eb43c54ce0003fff9d7eac42a348614000007ff88ab47988e68e000000010075776eada4e40000000001f957cc619b24000000000002bcb508db98000000000000021a758960000000000000000d77db40000000000000000021d7e00000000000000000003f400000000000000000000005f0a000
noncomputable def e33n_target1 : Nat := 0x1e60000000000000000004d01000
noncomputable def e33n_target2 : Nat := 0x300201000
noncomputable def e33n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 294
  maxLength := 10
  maxWidth := 95
  terms := 1
  left := e33n_left
  right := e33n_right
  scale := e33n_scale
  target0 := e33n_target0
  target1 := e33n_target1
  target2 := e33n_target2

theorem e33n_ok : e33n.check=true := by decide +kernel
noncomputable def e33d_left_0 : Nat := 0x7ff3943c72685b806c506d541600891ac7608d00008ecf3ed4000000488f050000000044b60000000000f300000000000003807000
noncomputable def e33d_left : Nat → Nat
  | 0 => e33d_left_0
  | _ => 0
noncomputable def e33d_right_0 : Nat := 0x300201000
noncomputable def e33d_right : Nat → Nat
  | 0 => e33d_right_0
  | _ => 0
noncomputable def e33d_scale : Nat := 0x180000000000000003d01000
noncomputable def e33d_target0 : Nat := 0xffe72878e4d0b600201b141b550580000448d63b04680000008ecf3ed4000000000911e0a0000000000112d80000000000007980000000000000004307000
noncomputable def e33d_target1 : Nat := 0x300000000000003201000
noncomputable def e33d_target2 : Nat := 0x300201000
noncomputable def e33d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 209
  maxLength := 7
  maxWidth := 67
  terms := 1
  left := e33d_left
  right := e33d_right
  scale := e33d_scale
  target0 := e33d_target0
  target1 := e33d_target1
  target2 := e33d_target2

theorem e33d_ok : e33d.check=true := by decide +kernel
noncomputable def e34n_left_0 : Nat := 0x3fffff8c9687b4380052ae20e00005d5c7a8f6265215a5400ffff94af1df258b483ef00007ffe9d6b2a9599af9c0000003ffbffecacf22005800000001fe3e2faeba4ff80000000000fa63394168a60000000000005dd6a04ddc00000000000000140a6849c000000000000000136f3d4000000000000000000efab000000000000000000000610b000
noncomputable def e34n_left : Nat → Nat
  | 0 => e34n_left_0
  | _ => 0
noncomputable def e34n_right_0 : Nat := 0x300201000
noncomputable def e34n_right : Nat → Nat
  | 0 => e34n_right_0
  | _ => 0
noncomputable def e34n_scale : Nat := 0xf30000000000000000000000006401000
noncomputable def e34n_target0 : Nat := 0x1fffffc64b43da1c00295710600800017571ea3d89948569500001ffff295e3be4b16907de0000007ffe9d6b2a9599af9c000000001ffdfff656791002c00000000007f8f8bebae93fe0000000000001f4c67282d14c000000000000005dd6a04ddc00000000000000000a053424e0000000000000000004dbcf5000000000000000000001df56000000000000000000000006a0b000
noncomputable def e34n_target1 : Nat := 0x7980000000000000000000005b01000
noncomputable def e34n_target2 : Nat := 0x300201000
noncomputable def e34n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 328
  maxLength := 11
  maxWidth := 106
  terms := 1
  left := e34n_left
  right := e34n_right
  scale := e34n_scale
  target0 := e34n_target0
  target1 := e34n_target1
  target2 := e34n_target2

theorem e34n_ok : e34n.check=true := by decide +kernel
noncomputable def e34d_left_0 : Nat := 0x7ff3943c72685b806c506d541600891ac7608d00008ecf3ed4000000488f050000000044b60000000000f300000000000003807000
noncomputable def e34d_left : Nat → Nat
  | 0 => e34d_left_0
  | _ => 0
noncomputable def e34d_right_0 : Nat := 0x300201000
noncomputable def e34d_right : Nat → Nat
  | 0 => e34d_right_0
  | _ => 0
noncomputable def e34d_scale : Nat := 0x300000000000000003e01000
noncomputable def e34d_target0 : Nat := 0x7ff3943c72685b000806c506d541600000891ac7608d00000008ecf3ed4000000000488f050000000000044b60000000000000f300000000000000004407000
noncomputable def e34d_target1 : Nat := 0x300000000000003201000
noncomputable def e34d_target2 : Nat := 0x300201000
noncomputable def e34d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 212
  maxLength := 7
  maxWidth := 68
  terms := 1
  left := e34d_left
  right := e34d_right
  scale := e34d_scale
  target0 := e34d_target0
  target1 := e34d_target1
  target2 := e34d_target2

theorem e34d_ok : e34d.check=true := by decide +kernel
noncomputable def e35n_left_0 : Nat := 0x200000f75e1217f7ea7afc97fffc792de414cd2cc96401fffc230713fe6b3eae00007ffd2da0109f1ea50000001fea45f4b9695d6000000007fefe31c804780000000001fe30eb0a60000000000000539f9cb900000000000000077b259000000000000000067844000000000000000001fa0000000000000000000005a0b000
noncomputable def e35n_left : Nat → Nat
  | 0 => e35n_left_0
  | _ => 0
noncomputable def e35n_right_0 : Nat := 0x300201000
noncomputable def e35n_right : Nat → Nat
  | 0 => e35n_right_0
  | _ => 0
noncomputable def e35n_scale : Nat := 0xf30000000000000000000000006401000
noncomputable def e35n_target0 : Nat := 0x200000f75e1217f7ea7afc900007fffc792de414cd2cc964000001fffc230713fe6b3eae000000007ffd2da0109f1ea500000000001fea45f4b9695d60000000000007fefe31c8047800000000000001fe30eb0a600000000000000000539f9cb9000000000000000000077b25900000000000000000000678440000000000000000000001fa00000000000000000000000006a0b000
noncomputable def e35n_target1 : Nat := 0xf3000000000000000000005401000
noncomputable def e35n_target2 : Nat := 0x300201000
noncomputable def e35n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 328
  maxLength := 11
  maxWidth := 106
  terms := 1
  left := e35n_left
  right := e35n_right
  scale := e35n_scale
  target0 := e35n_target0
  target1 := e35n_target1
  target2 := e35n_target2

theorem e35n_ok : e35n.check=true := by decide +kernel
noncomputable def e35d_left_0 : Nat := 0x7ff3943c72685b806c506d541600891ac7608d00008ecf3ed4000000488f050000000044b60000000000f300000000000003807000
noncomputable def e35d_left : Nat → Nat
  | 0 => e35d_left_0
  | _ => 0
noncomputable def e35d_right_0 : Nat := 0x300201000
noncomputable def e35d_right : Nat → Nat
  | 0 => e35d_right_0
  | _ => 0
noncomputable def e35d_scale : Nat := 0x300000000000000003e01000
noncomputable def e35d_target0 : Nat := 0x7ff3943c72685b000806c506d541600000891ac7608d00000008ecf3ed4000000000488f050000000000044b60000000000000f300000000000000004407000
noncomputable def e35d_target1 : Nat := 0x300000000000003201000
noncomputable def e35d_target2 : Nat := 0x300201000
noncomputable def e35d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 212
  maxLength := 7
  maxWidth := 68
  terms := 1
  left := e35d_left
  right := e35d_right
  scale := e35d_scale
  target0 := e35d_target0
  target1 := e35d_target1
  target2 := e35d_target2

theorem e35d_ok : e35d.check=true := by decide +kernel
noncomputable def e36n_left_0 : Nat := 0x3ffffece23050c49d3c8d95ffffc0e966b14a78d10c0100043935c80e3c119900007fd043ec11bdf1840000004060b9c77c08ce8000000027d02258a74480000000001a56198182a000000000000ac51e9440000000000000046ca68400000000000000021b8c000000000000000000fd000000000000000000000590b000
noncomputable def e36n_left : Nat → Nat
  | 0 => e36n_left_0
  | _ => 0
noncomputable def e36n_right_0 : Nat := 0x300201000
noncomputable def e36n_right : Nat → Nat
  | 0 => e36n_right_0
  | _ => 0
noncomputable def e36n_scale : Nat := 0x798000000000000000000000006301000
noncomputable def e36n_target0 : Nat := 0xfffffb388c1431274f23650001ffffc0e966b14a78d10c0000040010e4d72038f0466400000007fd043ec11bdf18400000000010182e71df0233a0000000000027d02258a74480000000000000695866060a8000000000000000ac51e9440000000000000000011b29a1000000000000000000021b8c0000000000000000000003f4000000000000000000000000670b000
noncomputable def e36n_target1 : Nat := 0x1e6000000000000000000005501000
noncomputable def e36n_target2 : Nat := 0x300201000
noncomputable def e36n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 319
  maxLength := 11
  maxWidth := 103
  terms := 1
  left := e36n_left
  right := e36n_right
  scale := e36n_scale
  target0 := e36n_target0
  target1 := e36n_target1
  target2 := e36n_target2

theorem e36n_ok : e36n.check=true := by decide +kernel
noncomputable def e36d_left_0 : Nat := 0x7ff3943c72685b806c506d541600891ac7608d00008ecf3ed4000000488f050000000044b60000000000f300000000000003807000
noncomputable def e36d_left : Nat → Nat
  | 0 => e36d_left_0
  | _ => 0
noncomputable def e36d_right_0 : Nat := 0x300201000
noncomputable def e36d_right : Nat → Nat
  | 0 => e36d_right_0
  | _ => 0
noncomputable def e36d_scale : Nat := 0x180000000000000003d01000
noncomputable def e36d_target0 : Nat := 0xffe72878e4d0b600201b141b550580000448d63b04680000008ecf3ed4000000000911e0a0000000000112d80000000000007980000000000000004307000
noncomputable def e36d_target1 : Nat := 0x300000000000003201000
noncomputable def e36d_target2 : Nat := 0x300201000
noncomputable def e36d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 209
  maxLength := 7
  maxWidth := 67
  terms := 1
  left := e36d_left
  right := e36d_right
  scale := e36d_scale
  target0 := e36d_target0
  target1 := e36d_target1
  target2 := e36d_target2

theorem e36d_ok : e36d.check=true := by decide +kernel
noncomputable def e37n_left_0 : Nat := 0xfffff0183fb66680c72fb6dfffe6602557c794bef7d004006a3855a01838e1a7000080117c34611abcdf0000000fe16c4dbf40b51800000002799369a2196e000000000075be8c82456000000000000bc1f2aef000000000000000c5fce7c000000000000000164dd0000000000000000004430000000000000000000005b0b000
noncomputable def e37n_left : Nat → Nat
  | 0 => e37n_left_0
  | _ => 0
noncomputable def e37n_right_0 : Nat := 0x300201000
noncomputable def e37n_right : Nat → Nat
  | 0 => e37n_right_0
  | _ => 0
noncomputable def e37n_scale : Nat := 0x798000000000000000000000006301000
noncomputable def e37n_target0 : Nat := 0xfffff0183fb66680c72fb6c001fffe6602557c794bef7d000004006a3855a01838e1a7000000080117c34611abcdf0000000000fe16c4dbf40b51800000000002799369a2196e000000000000075be8c82456000000000000000bc1f2aef000000000000000000c5fce7c000000000000000000164dd000000000000000000000443000000000000000000000000670b000
noncomputable def e37n_target1 : Nat := 0x798000000000000000000005701000
noncomputable def e37n_target2 : Nat := 0x300201000
noncomputable def e37n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 319
  maxLength := 11
  maxWidth := 103
  terms := 1
  left := e37n_left
  right := e37n_right
  scale := e37n_scale
  target0 := e37n_target0
  target1 := e37n_target1
  target2 := e37n_target2

theorem e37n_ok : e37n.check=true := by decide +kernel
noncomputable def e37d_left_0 : Nat := 0x7ff3943c72685b806c506d541600891ac7608d00008ecf3ed4000000488f050000000044b60000000000f300000000000003807000
noncomputable def e37d_left : Nat → Nat
  | 0 => e37d_left_0
  | _ => 0
noncomputable def e37d_right_0 : Nat := 0x300201000
noncomputable def e37d_right : Nat → Nat
  | 0 => e37d_right_0
  | _ => 0
noncomputable def e37d_scale : Nat := 0x180000000000000003d01000
noncomputable def e37d_target0 : Nat := 0xffe72878e4d0b600201b141b550580000448d63b04680000008ecf3ed4000000000911e0a0000000000112d80000000000007980000000000000004307000
noncomputable def e37d_target1 : Nat := 0x300000000000003201000
noncomputable def e37d_target2 : Nat := 0x300201000
noncomputable def e37d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 209
  maxLength := 7
  maxWidth := 67
  terms := 1
  left := e37d_left
  right := e37d_right
  scale := e37d_scale
  target0 := e37d_target0
  target1 := e37d_target1
  target2 := e37d_target2

theorem e37d_ok : e37d.check=true := by decide +kernel
noncomputable def e38n_left_0 : Nat := 0x7ff91eb9189061ac00387f600003cc00000090000000002405000
noncomputable def e38n_left : Nat → Nat
  | 0 => e38n_left_0
  | _ => 0
noncomputable def e38n_right_0 : Nat := 0x300201000
noncomputable def e38n_right : Nat → Nat
  | 0 => e38n_right_0
  | _ => 0
noncomputable def e38n_scale : Nat := 0x3000000000002a01000
noncomputable def e38n_target0 : Nat := 0x1ffe47ae440089061ac00000e1fd80000003cc0000000024000000000002e05000
noncomputable def e38n_target1 : Nat := 0xc000000002001000
noncomputable def e38n_target2 : Nat := 0x300201000
noncomputable def e38n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 144
  maxLength := 5
  maxWidth := 46
  terms := 1
  left := e38n_left
  right := e38n_right
  scale := e38n_scale
  target0 := e38n_target0
  target1 := e38n_target1
  target2 := e38n_target2

theorem e38n_ok : e38n.check=true := by decide +kernel
noncomputable def e38d_left_0 : Nat := 0x300201000
noncomputable def e38d_left : Nat → Nat
  | 0 => e38d_left_0
  | _ => 0
noncomputable def e38d_right_0 : Nat := 0x300201000
noncomputable def e38d_right : Nat → Nat
  | 0 => e38d_right_0
  | _ => 0
noncomputable def e38d_scale : Nat := 0x30000a01000
noncomputable def e38d_target0 : Nat := 0x30000a01000
noncomputable def e38d_target1 : Nat := 0x300201000
noncomputable def e38d_target2 : Nat := 0x300201000
noncomputable def e38d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 30
  maxLength := 1
  maxWidth := 10
  terms := 1
  left := e38d_left
  right := e38d_right
  scale := e38d_scale
  target0 := e38d_target0
  target1 := e38d_target1
  target2 := e38d_target2

theorem e38d_ok : e38d.check=true := by decide +kernel
noncomputable def e39n_left_0 : Nat := 0x20005e5564c4acb37ffaedcd4f0f1801fbe371a7b75000079de529dd0000001c237dad0000000044e598000000000058b00000000000003e07000
noncomputable def e39n_left : Nat → Nat
  | 0 => e39n_left_0
  | _ => 0
noncomputable def e39n_right_0 : Nat := 0x300201000
noncomputable def e39n_right : Nat → Nat
  | 0 => e39n_right_0
  | _ => 0
noncomputable def e39n_scale : Nat := 0x7980000000000000004301000
noncomputable def e39n_target0 : Nat := 0x20005e5564c4acb3007ffaedcd4f0f180001fbe371a7b7500000079de529dd000000001c237dad000000000044e59800000000000058b0000000000000004607000
noncomputable def e39n_target1 : Nat := 0x79800000000000003b01000
noncomputable def e39n_target2 : Nat := 0x300201000
noncomputable def e39n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 218
  maxLength := 7
  maxWidth := 70
  terms := 1
  left := e39n_left
  right := e39n_right
  scale := e39n_scale
  target0 := e39n_target0
  target1 := e39n_target1
  target2 := e39n_target2

theorem e39n_ok : e39n.check=true := by decide +kernel
noncomputable def e39d_left_0 : Nat := 0x7ff3943c72685b806c506d541600891ac7608d00008ecf3ed4000000488f050000000044b60000000000f300000000000003807000
noncomputable def e39d_left : Nat → Nat
  | 0 => e39d_left_0
  | _ => 0
noncomputable def e39d_right_0 : Nat := 0x300201000
noncomputable def e39d_right : Nat → Nat
  | 0 => e39d_right_0
  | _ => 0
noncomputable def e39d_scale : Nat := 0x180000000000000003d01000
noncomputable def e39d_target0 : Nat := 0xffe72878e4d0b600201b141b550580000448d63b04680000008ecf3ed4000000000911e0a0000000000112d80000000000007980000000000000004307000
noncomputable def e39d_target1 : Nat := 0x300000000000003201000
noncomputable def e39d_target2 : Nat := 0x300201000
noncomputable def e39d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 209
  maxLength := 7
  maxWidth := 67
  terms := 1
  left := e39d_left
  right := e39d_right
  scale := e39d_scale
  target0 := e39d_target0
  target1 := e39d_target1
  target2 := e39d_target2

theorem e39d_ok : e39d.check=true := by decide +kernel
end ThomsonNegative.Certificate.Bridges.RFChecks
