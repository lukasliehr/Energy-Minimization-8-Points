import ThomsonNegative.Certificate.Correction.q09.Input
import ThomsonNegative.Certificate.Correction.SourceData04

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Compact.Packed
open ThomsonNegative.Certificate
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

noncomputable def norm17 : Nat := 0x2
noncomputable def inverse17 : TM := ⟨0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x4, true⟩
theorem inverse17_checked : sameTM (denominatorInverse context argument Source.r17d norm17) inverse17=true := by decide +kernel
theorem norm17_positive : 0 < norm17 := by decide +kernel
noncomputable def columns17 : List Nat := [0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000014, 0x1, 0x800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006]
theorem columns17_checked : allBelow 68 (fun j => let M := ratioTM context argument inverse17 (Source.r17n j) norm17 1; M.ok && Nat.beq (rangeX context M) (columns17.getD j 0))=true := by decide +kernel
noncomputable def center17_0 : Nat := 0xdd1d1b2324307fc22598079c542fd7ffffffffffffffffffffffffffffffffffffffffffffffffffff814c01000
noncomputable def model17_0 : TM := ⟨0x2e8e8d9192183fe112cc03ce2a17ebffffffffffffffffffffffffffffffffffffffffffffffffffffc, 0x2e8e8d9192183fe112cc03ce2a17ebffffffffffffffffffffffffffffffffffffffffffffffffffffc, 0x2e8e8d9192183fe112cc03ce2a17ebffffffffffffffffffffffffffffffffffffffffffffffffffffc, 0x4, true⟩
noncomputable def center17_1 : Nat := 0x312088303f80fc6d1f2e13b6745c3b00000000000000000000000000000000000000000000000000000414e01000
noncomputable def model17_1 : TM := ⟨0x89044181fc07e368f9709db3a2e1d800000000000000000000000000000000000000000000000000002, 0x89044181fc07e368f9709db3a2e1d800000000000000000000000000000000000000000000000000002, 0x89044181fc07e368f9709db3a2e1d800000000000000000000000000000000000000000000000000002, 0x4, true⟩
noncomputable def center17_2 : Nat := 0x101b056fe6a2b27c8b7bb114db34217ffffffffffffffffffffffffffffffffffffffffffffffffffffc14f01000
noncomputable def model17_2 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe80d82b7f351593e45bdd88a6d9a10bffffffffffffffffffffffffffffffffffffffffffffffffffffe, 0x17f27d480caea6c1ba4227759265ef400000000000000000000000000000000000000000000000000002, 0x17f27d480caea6c1ba4227759265ef400000000000000000000000000000000000000000000000000002, 0x4, true⟩
noncomputable def center17_3 : Nat := 0x6042510bde496c1c591000fe3caa13fffffffffffffffffffffffffffffffffffffffffffffffffffff214f01000
noncomputable def model17_3 : TM := ⟨0x10212885ef24b60e2c88007f1e5509fffffffffffffffffffffffffffffffffffffffffffffffffffff9, 0x10212885ef24b60e2c88007f1e5509fffffffffffffffffffffffffffffffffffffffffffffffffffff9, 0x10212885ef24b60e2c88007f1e5509fffffffffffffffffffffffffffffffffffffffffffffffffffff9, 0x4, true⟩
noncomputable def center17_4 : Nat := 0xc906e84554217286afe533d4c36a1b00000000000000000000000000000000000000000000000000000015001000
noncomputable def model17_4 : TM := ⟨0x24837422aa10b94357f299ea61b50d800000000000000000000000000000000000000000000000000000, 0x24837422aa10b94357f299ea61b50d800000000000000000000000000000000000000000000000000000, 0x24837422aa10b94357f299ea61b50d800000000000000000000000000000000000000000000000000000, 0x4, true⟩
noncomputable def center17_5 : Nat := 0x7b0c8c8d1d2f92cee82217ada04b9200000000000000000000000000000000000000000000000000000415101000
noncomputable def model17_5 : TM := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbd8646468e97c96774110bd6d025c9000000000000000000000000000000000000000000000000000002, 0x4279b9b9716836988beef4292fda36fffffffffffffffffffffffffffffffffffffffffffffffffffffe, 0x4279b9b9716836988beef4292fda36fffffffffffffffffffffffffffffffffffffffffffffffffffffe, 0x4, true⟩
noncomputable def center17_6 : Nat := 0x1ad19fad459d8c7429da09426c802f00000000000000000000000000000000000000000000000000000a14d01000
noncomputable def model17_6 : TM := ⟨0x568cfd6a2cec63a14ed04a1364017800000000000000000000000000000000000000000000000000005, 0x568cfd6a2cec63a14ed04a1364017800000000000000000000000000000000000000000000000000005, 0x568cfd6a2cec63a14ed04a1364017800000000000000000000000000000000000000000000000000005, 0x4, true⟩
noncomputable def center17_7 : Nat := 0xd060c10171f5eff7a8fd8e9899fb3400000000000000000000000000000000000000000000000000000a15001000
noncomputable def model17_7 : TM := ⟨0x28306080b8faf7fbd47ec74c4cfd9a000000000000000000000000000000000000000000000000000005, 0x28306080b8faf7fbd47ec74c4cfd9a000000000000000000000000000000000000000000000000000005, 0x28306080b8faf7fbd47ec74c4cfd9a000000000000000000000000000000000000000000000000000005, 0x4, true⟩
noncomputable def center17_8 : Nat := 0xa8e1408fab36abf8b45c65e92c8577ffffffffffffffffffffffffffffffffffffffffffffffffffffc14e01000
noncomputable def model17_8 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff5470a047d59b55fc5a2e32f49642bbffffffffffffffffffffffffffffffffffffffffffffffffffffe, 0xab8f5fb82a64aa03a5d1cd0b69bd4400000000000000000000000000000000000000000000000000002, 0xab8f5fb82a64aa03a5d1cd0b69bd4400000000000000000000000000000000000000000000000000002, 0x4, true⟩
noncomputable def center17_9 : Nat := 0xc48d76ab6fc3062bcc1af76f04eeafffffffffffffffffffffffffffffffffffffffffffffffffffffc14e01000
noncomputable def model17_9 : TM := ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6246bb55b7e18315e60d7bb7827757ffffffffffffffffffffffffffffffffffffffffffffffffffffe, 0x9db944aa481e7cea19f284487d88a800000000000000000000000000000000000000000000000000002, 0x9db944aa481e7cea19f284487d88a800000000000000000000000000000000000000000000000000002, 0x4, true⟩
noncomputable def center17_10 : Nat := 0x306e64ec33e9117a9952f6d473483f80000000000000000000000000000000000000000000000000000814e01000
noncomputable def model17_10 : TM := ⟨0x837327619f488bd4ca97b6a39a41fc00000000000000000000000000000000000000000000000000004, 0x837327619f488bd4ca97b6a39a41fc00000000000000000000000000000000000000000000000000004, 0x837327619f488bd4ca97b6a39a41fc00000000000000000000000000000000000000000000000000004, 0x4, true⟩
noncomputable def centers17 : Nat → Nat
  | 0 => center17_0
  | 1 => center17_1
  | 2 => center17_2
  | 3 => center17_3
  | 4 => center17_4
  | 5 => center17_5
  | 6 => center17_6
  | 7 => center17_7
  | 8 => center17_8
  | 9 => center17_9
  | 10 => center17_10
  | _ => 0x100000
noncomputable def models17 : Nat → TM
  | 0 => model17_0
  | 1 => model17_1
  | 2 => model17_2
  | 3 => model17_3
  | 4 => model17_4
  | 5 => model17_5
  | 6 => model17_6
  | 7 => model17_7
  | 8 => model17_8
  | 9 => model17_9
  | 10 => model17_10
  | _ => zeroTM
theorem centers17_checked : allBelow 11 (fun k => sameTM (ratioTM context argument inverse17 (centers17 k) norm17 (Nat.pow 2 384)) (models17 k))=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
