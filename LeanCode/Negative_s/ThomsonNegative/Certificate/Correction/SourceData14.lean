import ThomsonNegative.Structure.Packed.IdentityKernel

namespace ThomsonNegative.Certificate.Correction.Source
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

noncomputable def r56n59 : Nat := 0x80e3c08b4800044b039e40000017030600000001e5b000000000003504000
noncomputable def r56n65 : Nat := 0x7fb8a7f9c67fdb21f86ce4afe2178008727ed668d4000016b61cd570000000c04feda00000000075398000000000003e06000
noncomputable def r56n67 : Nat := 0x2011d6018e60093c0f2636a03bd10078d8129972c00014a4f19548000000fec049800000007158d000000000003b06000
noncomputable def r56d : Nat := 0x80e3c08b4800022581cf20000005c0c1800000003cb6000000000003604000
noncomputable def r56n : Nat → Nat
  | 59 => r56n59
  | 65 => r56n65
  | 67 => r56n67
  | _ => 0x100000
theorem r56_headers : recordOk 6 62 r56d && allBelow 68 (fun j => recordOk 6 62 (r56n j)) = true := by decide +kernel
noncomputable def r57n61 : Nat := 0x80e3c08b4800022581cf20000005c0c1800000003cb6000000000003604000
noncomputable def r57n65 : Nat := 0x200c7c344a10067440a9abfd690458007afda69e9d20000134042b54c00000014bed00400000000628af8000000000003f06000
noncomputable def r57n67 : Nat := 0x7fce0f2ed7bfe637eaca8052df75008502596162e000065fdea55a000000ad04bff000000003aea1000000000003c06000
noncomputable def r57d : Nat := 0x80e3c08b48000112c0e7900000017030600000000796c000000000003704000
noncomputable def r57n : Nat → Nat
  | 61 => r57n61
  | 65 => r57n65
  | 67 => r57n67
  | _ => 0x100000
theorem r57_headers : recordOk 6 63 r57d && allBelow 68 (fun j => recordOk 6 63 (r57n j)) = true := by decide +kernel
noncomputable def r58n53 : Nat := 0x7f1c3f74b80000ed3f18700000028fcfa000000000694000000000003704000
noncomputable def r58n58 : Nat := 0x80c02a7584c00010fd2c361800000186a8d10000000070732000000000003b04000
noncomputable def r58n65 : Nat := 0x20108eae50d68946c40d699d275f63e80079ad53ee01de00001452a7249d40000000fd24b05c0000000071a7c48000000000004306000
noncomputable def r58n67 : Nat := 0x7fbdc546bca5dae57e52cc5b141383008652ac11fe2200005d6ac6db16000000c0b6d3e9000000001cb077000000000004006000
noncomputable def r58d : Nat := 0x80c02a7584c00010fd2c361800000186a8d10000000070732000000000003b04000
noncomputable def r58n : Nat → Nat
  | 53 => r58n53
  | 58 => r58n58
  | 65 => r58n65
  | 67 => r58n67
  | _ => 0x100000
theorem r58_headers : recordOk 6 67 r58d && allBelow 68 (fun j => recordOk 6 67 (r58n j)) = true := by decide +kernel
noncomputable def r59n62 : Nat := 0x80e3c08b4800044b039e40000017030600000001e5b000000000003504000
noncomputable def r59n65 : Nat := 0x803913382e001d88183d243392e8007a4675478f000009db93d5500000004c8cdb800000000cef48000000000003c06000
noncomputable def r59n67 : Nat := 0x1ff1bb31f47ff8afcf85b798da30085b98ab8710000312361558000002cdcc92000000006217000000000003906000
noncomputable def r59d : Nat := 0x80e3c08b4800022581cf20000005c0c1800000003cb6000000000003604000
noncomputable def r59n : Nat → Nat
  | 62 => r59n62
  | 65 => r59n65
  | 67 => r59n67
  | _ => 0x100000
theorem r59_headers : recordOk 6 60 r59d && allBelow 68 (fun j => recordOk 6 60 (r59n j)) = true := by decide +kernel
end ThomsonNegative.Certificate.Correction.Source
