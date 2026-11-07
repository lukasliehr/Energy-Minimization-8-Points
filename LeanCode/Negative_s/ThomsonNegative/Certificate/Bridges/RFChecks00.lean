import ThomsonNegative.Structure.Packed.IdentityKernel
namespace ThomsonNegative.Certificate.Bridges.RFChecks
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
noncomputable def e0n_left_0 : Nat := 0x100000
noncomputable def e0n_left : Nat → Nat
  | 0 => e0n_left_0
  | _ => 0
noncomputable def e0n_right_0 : Nat := 0x300201000
noncomputable def e0n_right : Nat → Nat
  | 0 => e0n_right_0
  | _ => 0
noncomputable def e0n_scale : Nat := 0x300201000
noncomputable def e0n_target0 : Nat := 0x100000
noncomputable def e0n_target1 : Nat := 0x300201000
noncomputable def e0n_target2 : Nat := 0x300201000
noncomputable def e0n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 6
  maxLength := 1
  maxWidth := 2
  terms := 1
  left := e0n_left
  right := e0n_right
  scale := e0n_scale
  target0 := e0n_target0
  target1 := e0n_target1
  target2 := e0n_target2

theorem e0n_ok : e0n.check=true := by decide +kernel
noncomputable def e0d_left_0 : Nat := 0x300201000
noncomputable def e0d_left : Nat → Nat
  | 0 => e0d_left_0
  | _ => 0
noncomputable def e0d_right_0 : Nat := 0x300201000
noncomputable def e0d_right : Nat → Nat
  | 0 => e0d_right_0
  | _ => 0
noncomputable def e0d_scale : Nat := 0x30000a01000
noncomputable def e0d_target0 : Nat := 0x30000a01000
noncomputable def e0d_target1 : Nat := 0x300201000
noncomputable def e0d_target2 : Nat := 0x300201000
noncomputable def e0d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 30
  maxLength := 1
  maxWidth := 10
  terms := 1
  left := e0d_left
  right := e0d_right
  scale := e0d_scale
  target0 := e0d_target0
  target1 := e0d_target1
  target2 := e0d_target2

theorem e0d_ok : e0d.check=true := by decide +kernel
noncomputable def e1n_left_0 : Nat := 0xd551607001000001303000
noncomputable def e1n_left : Nat → Nat
  | 0 => e1n_left_0
  | _ => 0
noncomputable def e1n_right_0 : Nat := 0x300201000
noncomputable def e1n_right : Nat → Nat
  | 0 => e1n_right_0
  | _ => 0
noncomputable def e1n_scale : Nat := 0x600000001b01000
noncomputable def e1n_target0 : Nat := 0xd551402070000100000001b03000
noncomputable def e1n_target1 : Nat := 0x6000001301000
noncomputable def e1n_target2 : Nat := 0x300201000
noncomputable def e1n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 85
  maxLength := 3
  maxWidth := 27
  terms := 1
  left := e1n_left
  right := e1n_right
  scale := e1n_scale
  target0 := e1n_target0
  target1 := e1n_target1
  target2 := e1n_target2

theorem e1n_ok : e1n.check=true := by decide +kernel
noncomputable def e1d_left_0 : Nat := 0x300201000
noncomputable def e1d_left : Nat → Nat
  | 0 => e1d_left_0
  | _ => 0
noncomputable def e1d_right_0 : Nat := 0x300201000
noncomputable def e1d_right : Nat → Nat
  | 0 => e1d_right_0
  | _ => 0
noncomputable def e1d_scale : Nat := 0x60000b01000
noncomputable def e1d_target0 : Nat := 0x60000b01000
noncomputable def e1d_target1 : Nat := 0x300201000
noncomputable def e1d_target2 : Nat := 0x300201000
noncomputable def e1d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 33
  maxLength := 1
  maxWidth := 11
  terms := 1
  left := e1d_left
  right := e1d_right
  scale := e1d_scale
  target0 := e1d_target0
  target1 := e1d_target1
  target2 := e1d_target2

theorem e1d_ok : e1d.check=true := by decide +kernel
noncomputable def e2n_left_0 : Nat := 0x3e224119ad7dd4b7f800e92378000274e0000001d0000000002705000
noncomputable def e2n_left : Nat → Nat
  | 0 => e2n_left_0
  | _ => 0
noncomputable def e2n_right_0 : Nat := 0x300201000
noncomputable def e2n_right : Nat → Nat
  | 0 => e2n_right_0
  | _ => 0
noncomputable def e2n_scale : Nat := 0x18000000000002d01000
noncomputable def e2n_target0 : Nat := 0x3e224119ad007dd4b7f80000e9237800000274e000000001d000000000002f05000
noncomputable def e2n_target1 : Nat := 0x180000000002501000
noncomputable def e2n_target2 : Nat := 0x300201000
noncomputable def e2n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 147
  maxLength := 5
  maxWidth := 47
  terms := 1
  left := e2n_left
  right := e2n_right
  scale := e2n_scale
  target0 := e2n_target0
  target1 := e2n_target1
  target2 := e2n_target2

theorem e2n_ok : e2n.check=true := by decide +kernel
noncomputable def e2d_left_0 : Nat := 0x300201000
noncomputable def e2d_left : Nat → Nat
  | 0 => e2d_left_0
  | _ => 0
noncomputable def e2d_right_0 : Nat := 0x300201000
noncomputable def e2d_right : Nat → Nat
  | 0 => e2d_right_0
  | _ => 0
noncomputable def e2d_scale : Nat := 0x180000d01000
noncomputable def e2d_target0 : Nat := 0x180000d01000
noncomputable def e2d_target1 : Nat := 0x300201000
noncomputable def e2d_target2 : Nat := 0x300201000
noncomputable def e2d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 39
  maxLength := 1
  maxWidth := 13
  terms := 1
  left := e2d_left
  right := e2d_right
  scale := e2d_scale
  target0 := e2d_target0
  target1 := e2d_target1
  target2 := e2d_target2

theorem e2d_ok : e2d.check=true := by decide +kernel
noncomputable def e3n_left_0 : Nat := 0x1f52e5d4c0e30f5598657008dd7d6d00001ab9f80000037ca00000000b000000000002d06000
noncomputable def e3n_left : Nat → Nat
  | 0 => e3n_left_0
  | _ => 0
noncomputable def e3n_right_0 : Nat := 0x300201000
noncomputable def e3n_right : Nat → Nat
  | 0 => e3n_right_0
  | _ => 0
noncomputable def e3n_scale : Nat := 0x1800000000000003501000
noncomputable def e3n_target0 : Nat := 0x1f52e5d4c0e2010f559865700008dd7d6d0000001ab9f8000000037ca0000000000b00000000000003506000
noncomputable def e3n_target1 : Nat := 0x18000000000002d01000
noncomputable def e3n_target2 : Nat := 0x300201000
noncomputable def e3n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 166
  maxLength := 6
  maxWidth := 53
  terms := 1
  left := e3n_left
  right := e3n_right
  scale := e3n_scale
  target0 := e3n_target0
  target1 := e3n_target1
  target2 := e3n_target2

theorem e3n_ok : e3n.check=true := by decide +kernel
noncomputable def e3d_left_0 : Nat := 0x300201000
noncomputable def e3d_left : Nat → Nat
  | 0 => e3d_left_0
  | _ => 0
noncomputable def e3d_right_0 : Nat := 0x300201000
noncomputable def e3d_right : Nat → Nat
  | 0 => e3d_right_0
  | _ => 0
noncomputable def e3d_scale : Nat := 0x180000d01000
noncomputable def e3d_target0 : Nat := 0x180000d01000
noncomputable def e3d_target1 : Nat := 0x300201000
noncomputable def e3d_target2 : Nat := 0x300201000
noncomputable def e3d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 39
  maxLength := 1
  maxWidth := 13
  terms := 1
  left := e3d_left
  right := e3d_right
  scale := e3d_scale
  target0 := e3d_target0
  target1 := e3d_target1
  target2 := e3d_target2

theorem e3d_ok : e3d.check=true := by decide +kernel
noncomputable def e4n_left_0 : Nat := 0x3f3b4d0effaf745fb6d19014d8400fb46bc65e7000085cac1be0000002c8393c00000003694400000000001900000000000003907000
noncomputable def e4n_left : Nat → Nat
  | 0 => e4n_left_0
  | _ => 0
noncomputable def e4n_right_0 : Nat := 0x300201000
noncomputable def e4n_right : Nat → Nat
  | 0 => e4n_right_0
  | _ => 0
noncomputable def e4n_scale : Nat := 0x300000000000000003e01000
noncomputable def e4n_target0 : Nat := 0x3f3b4d0effaf74401fb6d19014d840000fb46bc65e700000085cac1be000000002c8393c00000000036944000000000000190000000000000004107000
noncomputable def e4n_target1 : Nat := 0x3000000000000003601000
noncomputable def e4n_target2 : Nat := 0x300201000
noncomputable def e4n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 203
  maxLength := 7
  maxWidth := 65
  terms := 1
  left := e4n_left
  right := e4n_right
  scale := e4n_scale
  target0 := e4n_target0
  target1 := e4n_target1
  target2 := e4n_target2

theorem e4n_ok : e4n.check=true := by decide +kernel
noncomputable def e4d_left_0 : Nat := 0x300201000
noncomputable def e4d_left : Nat → Nat
  | 0 => e4d_left_0
  | _ => 0
noncomputable def e4d_right_0 : Nat := 0x300201000
noncomputable def e4d_right : Nat → Nat
  | 0 => e4d_right_0
  | _ => 0
noncomputable def e4d_scale : Nat := 0x300000e01000
noncomputable def e4d_target0 : Nat := 0x300000e01000
noncomputable def e4d_target1 : Nat := 0x300201000
noncomputable def e4d_target2 : Nat := 0x300201000
noncomputable def e4d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 42
  maxLength := 1
  maxWidth := 14
  terms := 1
  left := e4d_left
  right := e4d_right
  scale := e4d_scale
  target0 := e4d_target0
  target1 := e4d_target1
  target2 := e4d_target2

theorem e4d_ok : e4d.check=true := by decide +kernel
noncomputable def e5n_left_0 : Nat := 0x300201000
noncomputable def e5n_left : Nat → Nat
  | 0 => e5n_left_0
  | _ => 0
noncomputable def e5n_right_0 : Nat := 0x300201000
noncomputable def e5n_right : Nat → Nat
  | 0 => e5n_right_0
  | _ => 0
noncomputable def e5n_scale : Nat := 0x30000a01000
noncomputable def e5n_target0 : Nat := 0x30000a01000
noncomputable def e5n_target1 : Nat := 0x300201000
noncomputable def e5n_target2 : Nat := 0x300201000
noncomputable def e5n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 30
  maxLength := 1
  maxWidth := 10
  terms := 1
  left := e5n_left
  right := e5n_right
  scale := e5n_scale
  target0 := e5n_target0
  target1 := e5n_target1
  target2 := e5n_target2

theorem e5n_ok : e5n.check=true := by decide +kernel
noncomputable def e5d_left_0 : Nat := 0x300201000
noncomputable def e5d_left : Nat → Nat
  | 0 => e5d_left_0
  | _ => 0
noncomputable def e5d_right_0 : Nat := 0x300201000
noncomputable def e5d_right : Nat → Nat
  | 0 => e5d_right_0
  | _ => 0
noncomputable def e5d_scale : Nat := 0x30000a01000
noncomputable def e5d_target0 : Nat := 0x30000a01000
noncomputable def e5d_target1 : Nat := 0x300201000
noncomputable def e5d_target2 : Nat := 0x300201000
noncomputable def e5d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 30
  maxLength := 1
  maxWidth := 10
  terms := 1
  left := e5d_left
  right := e5d_right
  scale := e5d_scale
  target0 := e5d_target0
  target1 := e5d_target1
  target2 := e5d_target2

theorem e5d_ok : e5d.check=true := by decide +kernel
noncomputable def e6n_left_0 : Nat := 0x20390000b02000
noncomputable def e6n_left : Nat → Nat
  | 0 => e6n_left_0
  | _ => 0
noncomputable def e6n_right_0 : Nat := 0x300201000
noncomputable def e6n_right : Nat → Nat
  | 0 => e6n_right_0
  | _ => 0
noncomputable def e6n_scale : Nat := 0x63000001701000
noncomputable def e6n_target0 : Nat := 0x2038004000001502000
noncomputable def e6n_target1 : Nat := 0x18c000d01000
noncomputable def e6n_target2 : Nat := 0x300201000
noncomputable def e6n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 72
  maxLength := 2
  maxWidth := 23
  terms := 1
  left := e6n_left
  right := e6n_right
  scale := e6n_scale
  target0 := e6n_target0
  target1 := e6n_target1
  target2 := e6n_target2

theorem e6n_ok : e6n.check=true := by decide +kernel
noncomputable def e6d_left_0 : Nat := 0x808ad2030b6e4401a8580006300000001f04000
noncomputable def e6d_left : Nat → Nat
  | 0 => e6d_left_0
  | _ => 0
noncomputable def e6d_right_0 : Nat := 0x300201000
noncomputable def e6d_right : Nat → Nat
  | 0 => e6d_right_0
  | _ => 0
noncomputable def e6d_scale : Nat := 0x30000000002201000
noncomputable def e6d_target0 : Nat := 0x808ad202010b6e440001a85800000630000000002704000
noncomputable def e6d_target1 : Nat := 0x300000001a01000
noncomputable def e6d_target2 : Nat := 0x300201000
noncomputable def e6d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 123
  maxLength := 4
  maxWidth := 39
  terms := 1
  left := e6d_left
  right := e6d_right
  scale := e6d_scale
  target0 := e6d_target0
  target1 := e6d_target1
  target2 := e6d_target2

theorem e6d_ok : e6d.check=true := by decide +kernel
noncomputable def e7n_left_0 : Nat := 0x103111e7ab85898920029a2c80003308000000b0000000002505000
noncomputable def e7n_left : Nat → Nat
  | 0 => e7n_left_0
  | _ => 0
noncomputable def e7n_right_0 : Nat := 0x300201000
noncomputable def e7n_right : Nat → Nat
  | 0 => e7n_right_0
  | _ => 0
noncomputable def e7n_scale : Nat := 0x63000000000002f01000
noncomputable def e7n_target0 : Nat := 0x103111e7ab008589892000029a2c800000330800000000b000000000002d05000
noncomputable def e7n_target1 : Nat := 0x630000000002701000
noncomputable def e7n_target2 : Nat := 0x300201000
noncomputable def e7n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 147
  maxLength := 5
  maxWidth := 47
  terms := 1
  left := e7n_left
  right := e7n_right
  scale := e7n_scale
  target0 := e7n_target0
  target1 := e7n_target1
  target2 := e7n_target2

theorem e7n_ok : e7n.check=true := by decide +kernel
noncomputable def e7d_left_0 : Nat := 0x808ad2030b6e4401a8580006300000001f04000
noncomputable def e7d_left : Nat → Nat
  | 0 => e7d_left_0
  | _ => 0
noncomputable def e7d_right_0 : Nat := 0x300201000
noncomputable def e7d_right : Nat → Nat
  | 0 => e7d_right_0
  | _ => 0
noncomputable def e7d_scale : Nat := 0x30000000002201000
noncomputable def e7d_target0 : Nat := 0x808ad202010b6e440001a85800000630000000002704000
noncomputable def e7d_target1 : Nat := 0x300000001a01000
noncomputable def e7d_target2 : Nat := 0x300201000
noncomputable def e7d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 123
  maxLength := 4
  maxWidth := 39
  terms := 1
  left := e7d_left
  right := e7d_right
  scale := e7d_scale
  target0 := e7d_target0
  target1 := e7d_target1
  target2 := e7d_target2

theorem e7d_ok : e7d.check=true := by decide +kernel
noncomputable def e8n_left_0 : Nat := 0x1ff3cd9803796fe6ce9774d0082e560df000033026280000032d0e0000000019000000000003106000
noncomputable def e8n_left : Nat → Nat
  | 0 => e8n_left_0
  | _ => 0
noncomputable def e8n_right_0 : Nat := 0x300201000
noncomputable def e8n_right : Nat → Nat
  | 0 => e8n_right_0
  | _ => 0
noncomputable def e8n_scale : Nat := 0xc600000000000003801000
noncomputable def e8n_target0 : Nat := 0x1ff3cd980379600fe6ce9774d000082e560df0000003302628000000032d0e00000000001900000000000003906000
noncomputable def e8n_target1 : Nat := 0xc6000000000003001000
noncomputable def e8n_target2 : Nat := 0x300201000
noncomputable def e8n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 178
  maxLength := 6
  maxWidth := 57
  terms := 1
  left := e8n_left
  right := e8n_right
  scale := e8n_scale
  target0 := e8n_target0
  target1 := e8n_target1
  target2 := e8n_target2

theorem e8n_ok : e8n.check=true := by decide +kernel
noncomputable def e8d_left_0 : Nat := 0x808ad2030b6e4401a8580006300000001f04000
noncomputable def e8d_left : Nat → Nat
  | 0 => e8d_left_0
  | _ => 0
noncomputable def e8d_right_0 : Nat := 0x300201000
noncomputable def e8d_right : Nat → Nat
  | 0 => e8d_right_0
  | _ => 0
noncomputable def e8d_scale : Nat := 0x60000000002301000
noncomputable def e8d_target0 : Nat := 0x808ad2020085b72200006a16000000c60000000002804000
noncomputable def e8d_target1 : Nat := 0x300000001a01000
noncomputable def e8d_target2 : Nat := 0x300201000
noncomputable def e8d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 126
  maxLength := 4
  maxWidth := 40
  terms := 1
  left := e8d_left
  right := e8d_right
  scale := e8d_scale
  target0 := e8d_target0
  target1 := e8d_target1
  target2 := e8d_target2

theorem e8d_ok : e8d.check=true := by decide +kernel
noncomputable def e9n_left_0 : Nat := 0x20390000b02000
noncomputable def e9n_left : Nat → Nat
  | 0 => e9n_left_0
  | _ => 0
noncomputable def e9n_right_0 : Nat := 0x300201000
noncomputable def e9n_right : Nat → Nat
  | 0 => e9n_right_0
  | _ => 0
noncomputable def e9n_scale : Nat := 0x63000001701000
noncomputable def e9n_target0 : Nat := 0x2038004000001502000
noncomputable def e9n_target1 : Nat := 0x18c000d01000
noncomputable def e9n_target2 : Nat := 0x300201000
noncomputable def e9n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 72
  maxLength := 2
  maxWidth := 23
  terms := 1
  left := e9n_left
  right := e9n_right
  scale := e9n_scale
  target0 := e9n_target0
  target1 := e9n_target1
  target2 := e9n_target2

theorem e9n_ok : e9n.check=true := by decide +kernel
noncomputable def e9d_left_0 : Nat := 0x7edd0602f55e4401f8580006300000001f04000
noncomputable def e9d_left : Nat → Nat
  | 0 => e9d_left_0
  | _ => 0
noncomputable def e9d_right_0 : Nat := 0x300201000
noncomputable def e9d_right : Nat → Nat
  | 0 => e9d_right_0
  | _ => 0
noncomputable def e9d_scale : Nat := 0x30000000002201000
noncomputable def e9d_target0 : Nat := 0x7edd060200f55e440001f85800000630000000002704000
noncomputable def e9d_target1 : Nat := 0x300000001a01000
noncomputable def e9d_target2 : Nat := 0x300201000
noncomputable def e9d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 123
  maxLength := 4
  maxWidth := 39
  terms := 1
  left := e9d_left
  right := e9d_right
  scale := e9d_scale
  target0 := e9d_target0
  target1 := e9d_target1
  target2 := e9d_target2

theorem e9d_ok : e9d.check=true := by decide +kernel
end ThomsonNegative.Certificate.Bridges.RFChecks
