import ThomsonNegative.Certificate.Correction.q03.Input
import ThomsonNegative.Certificate.Correction.SourceData02

namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Compact.Packed
open ThomsonNegative.Certificate
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

noncomputable def norm11 : Nat := 0x2
noncomputable def inverse11 : TM := ⟨0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x4, true⟩
theorem inverse11_checked : sameTM (denominatorInverse context argument Source.r11d norm11) inverse11=true := by decide +kernel
theorem norm11_positive : 0 < norm11 := by decide +kernel
noncomputable def columns11 : List Nat := [0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a, 0x1, 0x1]
theorem columns11_checked : allBelow 68 (fun j => let M := ratioTM context argument inverse11 (Source.r11n j) norm11 1; M.ok && Nat.beq (rangeX context M) (columns11.getD j 0))=true := by decide +kernel
noncomputable def center11_0 : Nat := 0xa8adc7b2ed1ec175b1b80dd3517b6d49f10830e98df1c66448cee67deca175eb32d1d80943b47c0c414601000
noncomputable def model11_0 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff5456e3d9768f60bad8dc06e9a8bdb6a4f8841874c6f8e3322467733ef650baf59968ec04a1da3e062, 0xaba91c2689709f452723f9165742495b077be78b39071ccddb988cc109af450a669713fb5e25c1f9e, 0xaba91c2689709f452723f9165742495b077be78b39071ccddb988cc109af450a669713fb5e25c1f9e, 0x4, true⟩
noncomputable def center11_1 : Nat := 0x30ac305fc53c31e19f5c3c6e0de5cebc2992312b2926d166700cb4f0e740ad5371f51fe5b321863e57414a01000
noncomputable def model11_1 : TM := ⟨0x856182fe29e18f0cfae1e3706f2e75e14c91895949368b338065a7873a056a9b8fa8ff2d990c31f2ba, 0x856182fe29e18f0cfae1e3706f2e75e14c91895949368b338065a7873a056a9b8fa8ff2d990c31f2ba, 0x856182fe29e18f0cfae1e3706f2e75e14c91895949368b338065a7873a056a9b8fa8ff2d990c31f2ba, 0x4, true⟩
noncomputable def center11_2 : Nat := 0xc6a74225cd0fe13e8283d0664e0ec759289e0f4265a12dfa705e495aff8c2c898cb6ffb4361f4bd8e8c14c01000
noncomputable def model11_2 : TM := ⟨0x2353a112e687f09f4141e833270763ac944f07a132d096fd382f24ad7fc61644c65b7fda1b0fa5ec746, 0x2353a112e687f09f4141e833270763ac944f07a132d096fd382f24ad7fc61644c65b7fda1b0fa5ec746, 0x2353a112e687f09f4141e833270763ac944f07a132d096fd382f24ad7fc61644c65b7fda1b0fa5ec746, 0x4, true⟩
noncomputable def center11_3 : Nat := 0xebdb6c843ba06cf7738622d8058e55e411a2f13c5f4bc03048091635cf35eaa01f7b5b53a1491c383014b01000
noncomputable def model11_3 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe75edb6421dd0367bb9c3116c02c72af208d1789e2fa5e01824048b1ae79af5500fbdada9d0a48e1c18, 0x18a1249bde22fc984463cee93fd38d50df72e8761d05a1fe7dbfb74e518650aaff04252562f5b71e3e8, 0x18a1249bde22fc984463cee93fd38d50df72e8761d05a1fe7dbfb74e518650aaff04252562f5b71e3e8, 0x4, true⟩
noncomputable def center11_4 : Nat := 0x48afd7a8aefdc82e4afa2ec523ebbe1e821087a6d88013ae5a80bdbed89731e6e5b614583879b87a7014b01000
noncomputable def model11_4 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe2457ebd4577ee417257d176291f5df0f410843d36c4009d72d405edf6c4b98f372db0a2c1c3cdc3d38, 0x1dba8142ba8811be8da82e89d6e0a20f0bef7bc2c93bff628d2bfa12093b4670c8d24f5d3e3c323c2c8, 0x1dba8142ba8811be8da82e89d6e0a20f0bef7bc2c93bff628d2bfa12093b4670c8d24f5d3e3c323c2c8, 0x4, true⟩
noncomputable def center11_5 : Nat := 0x1b2a5049681be5a5557e0005167f78e18a750b8615a363962cacb8066761f134dc41492dcf5d1c96af414b01000
noncomputable def model11_5 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed952824b40df2d2aabf00028b3fbc70c53a85c30ad1b1cb16565c0333b0f89a6e20a496e7ae8e4b57a, 0x126ad7db4bf20d2d5540fffd74c0438f3ac57a3cf52e4e34e9a9a3fccc4f076591df5b69185171b4a86, 0x126ad7db4bf20d2d5540fffd74c0438f3ac57a3cf52e4e34e9a9a3fccc4f076591df5b69185171b4a86, 0x4, true⟩
noncomputable def center11_6 : Nat := 0xe9725d1f330a5995dfaea159a185595693736b96e50b1f28fcc1441c6105cd45342238ca5b0ad0093c14a01000
noncomputable def model11_6 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff74b92e8f99852ccaefd750acd0c2acab49b9b5cb72858f947e60a20e3082e6a29a111c652d8568049e, 0x8b46d170667ad3351028af532f3d5354b6464a348d7a706b819f5df1cf7d195d65eee39ad27a97fb62, 0x8b46d170667ad3351028af532f3d5354b6464a348d7a706b819f5df1cf7d195d65eee39ad27a97fb62, 0x4, true⟩
noncomputable def center11_7 : Nat := 0xc43105644f00e5d8e5f7674262086eb23f23616f17c451a806d43750cb76bde6ae7a5ef9382f261e20614c01000
noncomputable def model11_7 : TM := ⟨0x221882b2278072ec72fbb3a1310437591f91b0b78be228d4036a1ba865bb5ef3573d2f7c9c17930f103, 0x221882b2278072ec72fbb3a1310437591f91b0b78be228d4036a1ba865bb5ef3573d2f7c9c17930f103, 0x221882b2278072ec72fbb3a1310437591f91b0b78be228d4036a1ba865bb5ef3573d2f7c9c17930f103, 0x4, true⟩
noncomputable def center11_8 : Nat := 0x6927284248b36091383742d28e63d96b5848a9adcd2e0947cb54db44200226077727f05801e735a353a14b01000
noncomputable def model11_8 : TM := ⟨0x149394212459b0489c1ba1694731ecb5ac2454d6e69704a3e5aa6da210011303bb93f82c00f39ad1a9d, 0x149394212459b0489c1ba1694731ecb5ac2454d6e69704a3e5aa6da210011303bb93f82c00f39ad1a9d, 0x149394212459b0489c1ba1694731ecb5ac2454d6e69704a3e5aa6da210011303bb93f82c00f39ad1a9d, 0x4, true⟩
noncomputable def center11_9 : Nat := 0x59010fbee2ca0bf05105436753fbc64698dbd3d18a56ca5153e391e29dd50a5da85666565bed7f6f6a14901000
noncomputable def model11_9 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffac8087df716505f82882a1b3a9fde3234c6de9e8c52b6528a9f1c8f14eea852ed42b332b2df6bfb7b5, 0x537f78208e9afa07d77d5e4c56021cdcb39216173ad49ad7560e370eb1157ad12bd4ccd4d20940484b, 0x537f78208e9afa07d77d5e4c56021cdcb39216173ad49ad7560e370eb1157ad12bd4ccd4d20940484b, 0x4, true⟩
noncomputable def center11_10 : Nat := 0x6572fffeb48052b4c0fbd25360c8d11d617d4ae7df9ba3756747af8a8d14a038cfb6026bac2dd18dd214a01000
noncomputable def model11_10 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff32b97fff5a40295a607de929b064688eb0bea573efcdd1bab3a3d7c5468a501c67db0135d616e8c6e9, 0xcd468000a5bfd6a59f8216d64f9b97714f415a8c10322e454c5c283ab975afe39824feca29e9173917, 0xcd468000a5bfd6a59f8216d64f9b97714f415a8c10322e454c5c283ab975afe39824feca29e9173917, 0x4, true⟩
noncomputable def centers11 : Nat → Nat
  | 0 => center11_0
  | 1 => center11_1
  | 2 => center11_2
  | 3 => center11_3
  | 4 => center11_4
  | 5 => center11_5
  | 6 => center11_6
  | 7 => center11_7
  | 8 => center11_8
  | 9 => center11_9
  | 10 => center11_10
  | _ => 0x100000
noncomputable def models11 : Nat → TM
  | 0 => model11_0
  | 1 => model11_1
  | 2 => model11_2
  | 3 => model11_3
  | 4 => model11_4
  | 5 => model11_5
  | 6 => model11_6
  | 7 => model11_7
  | 8 => model11_8
  | 9 => model11_9
  | 10 => model11_10
  | _ => zeroTM
theorem centers11_checked : allBelow 11 (fun k => sameTM (ratioTM context argument inverse11 (centers11 k) norm11 (Nat.pow 2 384)) (models11 k))=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q03
