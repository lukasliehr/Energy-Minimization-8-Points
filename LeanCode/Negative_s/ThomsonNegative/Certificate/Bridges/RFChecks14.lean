import ThomsonNegative.Structure.Packed.IdentityKernel
namespace ThomsonNegative.Certificate.Bridges.RFChecks
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
noncomputable def e140n_left_0 : Nat := 0x200196fa08ecc004ce36bf007a84d6540000a3fc38000000c968000000043000000000002f06000
noncomputable def e140n_left : Nat → Nat
  | 0 => e140n_left_0
  | _ => 0
noncomputable def e140n_right_0 : Nat := 0x300201000
noncomputable def e140n_right : Nat → Nat
  | 0 => e140n_right_0
  | _ => 0
noncomputable def e140n_scale : Nat := 0x3400000000000003601000
noncomputable def e140n_target0 : Nat := 0x200196fa08ec8004004ce36bf000007a84d6540000000a3fc38000000000c968000000000043000000000000003b06000
noncomputable def e140n_target1 : Nat := 0x3400000000002a01000
noncomputable def e140n_target2 : Nat := 0x300201000
noncomputable def e140n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 184
  maxLength := 6
  maxWidth := 59
  terms := 1
  left := e140n_left
  right := e140n_right
  scale := e140n_scale
  target0 := e140n_target0
  target1 := e140n_target1
  target2 := e140n_target2

theorem e140n_ok : e140n.check=true := by decide +kernel
noncomputable def e140d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e140d_left : Nat → Nat
  | 0 => e140d_left_0
  | _ => 0
noncomputable def e140d_right_0 : Nat := 0x300201000
noncomputable def e140d_right : Nat → Nat
  | 0 => e140d_right_0
  | _ => 0
noncomputable def e140d_scale : Nat := 0xc00000000000003401000
noncomputable def e140d_target0 : Nat := 0x7f01731e38f001e55eca6a4000091edd260000002a06080000000001b00000000003400000000000003606000
noncomputable def e140d_target1 : Nat := 0x3000000000002a01000
noncomputable def e140d_target2 : Nat := 0x300201000
noncomputable def e140d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 169
  maxLength := 6
  maxWidth := 54
  terms := 1
  left := e140d_left
  right := e140d_right
  scale := e140d_scale
  target0 := e140d_target0
  target1 := e140d_target1
  target2 := e140d_target2

theorem e140d_ok : e140d.check=true := by decide +kernel
noncomputable def e141n_left_0 : Nat := 0x200033e83176d1157ff4ca136f572801fec3c8c058300008036b3e5b0000001ee5738b000000004d2ca80000000000b7d00000000000003e07000
noncomputable def e141n_left : Nat → Nat
  | 0 => e141n_left_0
  | _ => 0
noncomputable def e141n_right_0 : Nat := 0x300201000
noncomputable def e141n_right : Nat → Nat
  | 0 => e141n_right_0
  | _ => 0
noncomputable def e141n_scale : Nat := 0x680000000000000003f01000
noncomputable def e141n_target0 : Nat := 0x200033e83176d115007ff4ca136f57280001fec3c8c05830000008036b3e5b000000001ee5738b00000000004d2ca8000000000000b7d0000000000000004607000
noncomputable def e141n_target1 : Nat := 0x6800000000000003701000
noncomputable def e141n_target2 : Nat := 0x300201000
noncomputable def e141n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 218
  maxLength := 7
  maxWidth := 70
  terms := 1
  left := e141n_left
  right := e141n_right
  scale := e141n_scale
  target0 := e141n_target0
  target1 := e141n_target1
  target2 := e141n_target2

theorem e141n_ok : e141n.check=true := by decide +kernel
noncomputable def e141d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e141d_left : Nat → Nat
  | 0 => e141d_left_0
  | _ => 0
noncomputable def e141d_right_0 : Nat := 0x300201000
noncomputable def e141d_right : Nat → Nat
  | 0 => e141d_right_0
  | _ => 0
noncomputable def e141d_scale : Nat := 0x1800000000000003501000
noncomputable def e141d_target0 : Nat := 0x1fc05cc78e3c003cabd94d48000091edd2600000015030400000000006c00000000006800000000000003706000
noncomputable def e141d_target1 : Nat := 0x3000000000002a01000
noncomputable def e141d_target2 : Nat := 0x300201000
noncomputable def e141d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 172
  maxLength := 6
  maxWidth := 55
  terms := 1
  left := e141d_left
  right := e141d_right
  scale := e141d_scale
  target0 := e141d_target0
  target1 := e141d_target1
  target2 := e141d_target2

theorem e141d_ok : e141d.check=true := by decide +kernel
noncomputable def e142n_left_0 : Nat := 0xfffc1088fb212dffa22f5a32b004195be63bd0000a3c511a800000194a1540000000263b00000000004300000000000003707000
noncomputable def e142n_left : Nat → Nat
  | 0 => e142n_left_0
  | _ => 0
noncomputable def e142n_right_0 : Nat := 0x300201000
noncomputable def e142n_right : Nat → Nat
  | 0 => e142n_right_0
  | _ => 0
noncomputable def e142n_scale : Nat := 0x340000000000000003e01000
noncomputable def e142n_target0 : Nat := 0xfffc1088fb212c001ffa22f5a32b000004195be63bd0000000a3c511a800000000194a1540000000000263b00000000000004300000000000000004307000
noncomputable def e142n_target1 : Nat := 0x340000000000003201000
noncomputable def e142n_target2 : Nat := 0x300201000
noncomputable def e142n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 209
  maxLength := 7
  maxWidth := 67
  terms := 1
  left := e142n_left
  right := e142n_right
  scale := e142n_scale
  target0 := e142n_target0
  target1 := e142n_target1
  target2 := e142n_target2

theorem e142n_ok : e142n.check=true := by decide +kernel
noncomputable def e142d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e142d_left : Nat → Nat
  | 0 => e142d_left_0
  | _ => 0
noncomputable def e142d_right_0 : Nat := 0x300201000
noncomputable def e142d_right : Nat → Nat
  | 0 => e142d_right_0
  | _ => 0
noncomputable def e142d_scale : Nat := 0xc00000000000003401000
noncomputable def e142d_target0 : Nat := 0x7f01731e38f001e55eca6a4000091edd260000002a06080000000001b00000000003400000000000003606000
noncomputable def e142d_target1 : Nat := 0x3000000000002a01000
noncomputable def e142d_target2 : Nat := 0x300201000
noncomputable def e142d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 169
  maxLength := 6
  maxWidth := 54
  terms := 1
  left := e142d_left
  right := e142d_right
  scale := e142d_scale
  target0 := e142d_target0
  target1 := e142d_target1
  target2 := e142d_target2

theorem e142d_ok : e142d.check=true := by decide +kernel
noncomputable def e143n_left_0 : Nat := 0x3fffd372e401955ff4b2cb76e940104a74b5f430000a9d1dd36000000705a12c0000000221540000000000bd00000000000003907000
noncomputable def e143n_left : Nat → Nat
  | 0 => e143n_left_0
  | _ => 0
noncomputable def e143n_right_0 : Nat := 0x300201000
noncomputable def e143n_right : Nat → Nat
  | 0 => e143n_right_0
  | _ => 0
noncomputable def e143n_scale : Nat := 0x340000000000000003e01000
noncomputable def e143n_target0 : Nat := 0xffff4dcb900655001ff4b2cb76e9400004129d2d7d0c000000a9d1dd36000000001c1684b0000000000221540000000000002f40000000000000004307000
noncomputable def e143n_target1 : Nat := 0xd00000000000003401000
noncomputable def e143n_target2 : Nat := 0x300201000
noncomputable def e143n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 209
  maxLength := 7
  maxWidth := 67
  terms := 1
  left := e143n_left
  right := e143n_right
  scale := e143n_scale
  target0 := e143n_target0
  target1 := e143n_target1
  target2 := e143n_target2

theorem e143n_ok : e143n.check=true := by decide +kernel
noncomputable def e143d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e143d_left : Nat → Nat
  | 0 => e143d_left_0
  | _ => 0
noncomputable def e143d_right_0 : Nat := 0x300201000
noncomputable def e143d_right : Nat → Nat
  | 0 => e143d_right_0
  | _ => 0
noncomputable def e143d_scale : Nat := 0xc00000000000003401000
noncomputable def e143d_target0 : Nat := 0x7f01731e38f001e55eca6a4000091edd260000002a06080000000001b00000000003400000000000003606000
noncomputable def e143d_target1 : Nat := 0x3000000000002a01000
noncomputable def e143d_target2 : Nat := 0x300201000
noncomputable def e143d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 169
  maxLength := 6
  maxWidth := 54
  terms := 1
  left := e143d_left
  right := e143d_right
  scale := e143d_scale
  target0 := e143d_target0
  target1 := e143d_target1
  target2 := e143d_target2

theorem e143d_ok : e143d.check=true := by decide +kernel
noncomputable def e144n_left_0 : Nat := 0x2087115c58009000001603000
noncomputable def e144n_left : Nat → Nat
  | 0 => e144n_left_0
  | _ => 0
noncomputable def e144n_right_0 : Nat := 0x300201000
noncomputable def e144n_right : Nat → Nat
  | 0 => e144n_right_0
  | _ => 0
noncomputable def e144n_scale : Nat := 0x300000001a01000
noncomputable def e144n_target0 : Nat := 0x10438880171600001200000001f03000
noncomputable def e144n_target1 : Nat := 0x1800001101000
noncomputable def e144n_target2 : Nat := 0x300201000
noncomputable def e144n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 97
  maxLength := 3
  maxWidth := 31
  terms := 1
  left := e144n_left
  right := e144n_right
  scale := e144n_scale
  target0 := e144n_target0
  target1 := e144n_target1
  target2 := e144n_target2

theorem e144n_ok : e144n.check=true := by decide +kernel
noncomputable def e144d_left_0 : Nat := 0x54f0000a02000
noncomputable def e144d_left : Nat → Nat
  | 0 => e144d_left_0
  | _ => 0
noncomputable def e144d_right_0 : Nat := 0x300201000
noncomputable def e144d_right : Nat → Nat
  | 0 => e144d_right_0
  | _ => 0
noncomputable def e144d_scale : Nat := 0x3000001201000
noncomputable def e144d_target0 : Nat := 0x54c03000001202000
noncomputable def e144d_target1 : Nat := 0x30000a01000
noncomputable def e144d_target2 : Nat := 0x300201000
noncomputable def e144d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 57
  maxLength := 2
  maxWidth := 18
  terms := 1
  left := e144d_left
  right := e144d_right
  scale := e144d_scale
  target0 := e144d_target0
  target1 := e144d_target1
  target2 := e144d_target2

theorem e144d_ok : e144d.check=true := by decide +kernel
noncomputable def e145n_left_0 : Nat := 0x8005c954294f580337ba7ff30082d6651c2000098de8f6000000cb93900000000b27000000000003406000
noncomputable def e145n_left : Nat → Nat
  | 0 => e145n_left_0
  | _ => 0
noncomputable def e145n_right_0 : Nat := 0x300201000
noncomputable def e145n_right : Nat → Nat
  | 0 => e145n_right_0
  | _ => 0
noncomputable def e145n_scale : Nat := 0x7c00000000000003701000
noncomputable def e145n_target0 : Nat := 0x8005c954294f50080337ba7ff3000082d6651c200000098de8f600000000cb9390000000000b2700000000000003c06000
noncomputable def e145n_target1 : Nat := 0x7c000000000002f01000
noncomputable def e145n_target2 : Nat := 0x300201000
noncomputable def e145n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 187
  maxLength := 6
  maxWidth := 60
  terms := 1
  left := e145n_left
  right := e145n_right
  scale := e145n_scale
  target0 := e145n_target0
  target1 := e145n_target1
  target2 := e145n_target2

theorem e145n_ok : e145n.check=true := by decide +kernel
noncomputable def e145d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e145d_left : Nat → Nat
  | 0 => e145d_left_0
  | _ => 0
noncomputable def e145d_right_0 : Nat := 0x300201000
noncomputable def e145d_right : Nat → Nat
  | 0 => e145d_right_0
  | _ => 0
noncomputable def e145d_scale : Nat := 0x1c00000000000003501000
noncomputable def e145d_target0 : Nat := 0x7f411656aab4007b01c5f3ec00008d725dc80000009e12180000000021440000000000bc00000000000003806000
noncomputable def e145d_target1 : Nat := 0x3000000000002a01000
noncomputable def e145d_target2 : Nat := 0x300201000
noncomputable def e145d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 175
  maxLength := 6
  maxWidth := 56
  terms := 1
  left := e145d_left
  right := e145d_right
  scale := e145d_scale
  target0 := e145d_target0
  target1 := e145d_target1
  target2 := e145d_target2

theorem e145d_ok : e145d.check=true := by decide +kernel
noncomputable def e146n_left_0 : Nat := 0x2000861cddb83a18005464e5348801f9ca736ad700006e2638ef0000000f608ff000000003a0080000000001a900000000000003a07000
noncomputable def e146n_left : Nat → Nat
  | 0 => e146n_left_0
  | _ => 0
noncomputable def e146n_right_0 : Nat := 0x300201000
noncomputable def e146n_right : Nat → Nat
  | 0 => e146n_right_0
  | _ => 0
noncomputable def e146n_scale : Nat := 0x7c0000000000000003f01000
noncomputable def e146n_target0 : Nat := 0x8002187376e0e84008005464e5348800007e729cdab5c0000006e2638ef0000000003d823fc00000000003a0080000000000006a40000000000000004407000
noncomputable def e146n_target1 : Nat := 0x1f00000000000003501000
noncomputable def e146n_target2 : Nat := 0x300201000
noncomputable def e146n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 212
  maxLength := 7
  maxWidth := 68
  terms := 1
  left := e146n_left
  right := e146n_right
  scale := e146n_scale
  target0 := e146n_target0
  target1 := e146n_target1
  target2 := e146n_target2

theorem e146n_ok : e146n.check=true := by decide +kernel
noncomputable def e146d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e146d_left : Nat → Nat
  | 0 => e146d_left_0
  | _ => 0
noncomputable def e146d_right_0 : Nat := 0x300201000
noncomputable def e146d_right : Nat → Nat
  | 0 => e146d_right_0
  | _ => 0
noncomputable def e146d_scale : Nat := 0x1c00000000000003501000
noncomputable def e146d_target0 : Nat := 0x7f411656aab4007b01c5f3ec00008d725dc80000009e12180000000021440000000000bc00000000000003806000
noncomputable def e146d_target1 : Nat := 0x3000000000002a01000
noncomputable def e146d_target2 : Nat := 0x300201000
noncomputable def e146d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 175
  maxLength := 6
  maxWidth := 56
  terms := 1
  left := e146d_left
  right := e146d_right
  scale := e146d_scale
  target0 := e146d_target0
  target1 := e146d_target1
  target2 := e146d_target2

theorem e146d_ok : e146d.check=true := by decide +kernel
noncomputable def e147n_left_0 : Nat := 0x3ffe4bf764e9fdffe0b1dc37800fd486abdb00006764888000000159394000000013e80000000001100000000000003507000
noncomputable def e147n_left : Nat → Nat
  | 0 => e147n_left_0
  | _ => 0
noncomputable def e147n_right_0 : Nat := 0x300201000
noncomputable def e147n_right : Nat → Nat
  | 0 => e147n_right_0
  | _ => 0
noncomputable def e147n_scale : Nat := 0x7c0000000000000003f01000
noncomputable def e147n_target0 : Nat := 0x7ffc97eec9d3f80007ff82c770de0000007ea4355ed80000000676488800000000002b2728000000000004fa000000000000008800000000000000004407000
noncomputable def e147n_target1 : Nat := 0xf8000000000003001000
noncomputable def e147n_target2 : Nat := 0x300201000
noncomputable def e147n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 212
  maxLength := 7
  maxWidth := 68
  terms := 1
  left := e147n_left
  right := e147n_right
  scale := e147n_scale
  target0 := e147n_target0
  target1 := e147n_target1
  target2 := e147n_target2

theorem e147n_ok : e147n.check=true := by decide +kernel
noncomputable def e147d_left_0 : Nat := 0x7f01731e38f7957b29a90091edd260000a818200000001b00000000d000000000002c06000
noncomputable def e147d_left : Nat → Nat
  | 0 => e147d_left_0
  | _ => 0
noncomputable def e147d_right_0 : Nat := 0x300201000
noncomputable def e147d_right : Nat → Nat
  | 0 => e147d_right_0
  | _ => 0
noncomputable def e147d_scale : Nat := 0x1c00000000000003501000
noncomputable def e147d_target0 : Nat := 0x7f411656aab4007b01c5f3ec00008d725dc80000009e12180000000021440000000000bc00000000000003806000
noncomputable def e147d_target1 : Nat := 0x3000000000002a01000
noncomputable def e147d_target2 : Nat := 0x300201000
noncomputable def e147d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 175
  maxLength := 6
  maxWidth := 56
  terms := 1
  left := e147d_left
  right := e147d_right
  scale := e147d_scale
  target0 := e147d_target0
  target1 := e147d_target1
  target2 := e147d_target2

theorem e147d_ok : e147d.check=true := by decide +kernel
noncomputable def e148n_left_0 : Nat := 0x3ac77f214017000001503000
noncomputable def e148n_left : Nat → Nat
  | 0 => e148n_left_0
  | _ => 0
noncomputable def e148n_right_0 : Nat := 0x300201000
noncomputable def e148n_right : Nat → Nat
  | 0 => e148n_right_0
  | _ => 0
noncomputable def e148n_scale : Nat := 0x700000001b01000
noncomputable def e148n_target0 : Nat := 0x1d63be00c8500002e00000001e03000
noncomputable def e148n_target1 : Nat := 0x3800001201000
noncomputable def e148n_target2 : Nat := 0x300201000
noncomputable def e148n : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 94
  maxLength := 3
  maxWidth := 30
  terms := 1
  left := e148n_left
  right := e148n_right
  scale := e148n_scale
  target0 := e148n_target0
  target1 := e148n_target1
  target2 := e148n_target2

theorem e148n_ok : e148n.check=true := by decide +kernel
noncomputable def e148d_left_0 : Nat := 0x54f0000a02000
noncomputable def e148d_left : Nat → Nat
  | 0 => e148d_left_0
  | _ => 0
noncomputable def e148d_right_0 : Nat := 0x300201000
noncomputable def e148d_right : Nat → Nat
  | 0 => e148d_right_0
  | _ => 0
noncomputable def e148d_scale : Nat := 0x7000001301000
noncomputable def e148d_target0 : Nat := 0xfc807000001302000
noncomputable def e148d_target1 : Nat := 0x30000a01000
noncomputable def e148d_target2 : Nat := 0x300201000
noncomputable def e148d : ThomsonNegative.Structure.Exact.Equation where
  radixBits := 60
  maxLength := 2
  maxWidth := 19
  terms := 1
  left := e148d_left
  right := e148d_right
  scale := e148d_scale
  target0 := e148d_target0
  target1 := e148d_target1
  target2 := e148d_target2

theorem e148d_ok : e148d.check=true := by decide +kernel
end ThomsonNegative.Certificate.Bridges.RFChecks
