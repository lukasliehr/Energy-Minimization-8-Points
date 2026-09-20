import Thomson8.Interval
import Thomson8.Certificate

namespace Thomson8

theorem sqrt_in_box (b : Box) (n : ℚ) (hn : 0 ≤ n)
    (hlo : b.lo^2 ≤ n) (hhi : n ≤ b.hi^2) (hhip : 0 ≤ b.hi) :
    b.Contains (Real.sqrt (n : ℝ)) := by
  have hn' : (0 : ℝ) ≤ n := Rat.cast_nonneg.mpr hn
  have hs := Real.sq_sqrt hn'
  have hp := Real.sqrt_nonneg (n : ℝ)
  have hl : (b.lo : ℝ)^2 ≤ (n : ℝ) := by exact_mod_cast hlo
  have hu : (n : ℝ) ≤ (b.hi : ℝ)^2 := by exact_mod_cast hhi
  have hu' : (0 : ℝ) ≤ b.hi := Rat.cast_nonneg.mpr hhip
  constructor <;> nlinarith

def root2 : Box := ⟨(481231938336009023090067544955250113854/340282366920938463463374607431768211456),(481231938336009023090067544955250113855/340282366920938463463374607431768211456)⟩
theorem root2_contains : root2.Contains (Real.sqrt 2) := by
  apply sqrt_in_box root2 2 <;> norm_num [root2]

def root58 : Box := ⟨(2591513298396197567651868676209015848744/340282366920938463463374607431768211456),(2591513298396197567651868676209015848745/340282366920938463463374607431768211456)⟩
theorem root58_contains : root58.Contains (Real.sqrt 58) := by
  apply sqrt_in_box root58 58 <;> norm_num [root58]

def encloseK (x : K) : Box := Box.field root2 root58 x

theorem encloseK_contains (x : K) : (encloseK x).Contains x.eval :=
  Box.contains_field root2_contains root58_contains x

theorem nodes_interior (i : Fin 4) : -1 < ((nodes.getD i K.zero).eval) ∧
    ((nodes.getD i K.zero).eval) < 1 := by
  have h := encloseK_contains (nodes.getD i K.zero)
  have hb : (-1 : ℚ) < (encloseK (nodes.getD i K.zero)).lo ∧
      (encloseK (nodes.getD i K.zero)).hi < 1 := by
    fin_cases i <;> decide +kernel
  have hl : (-1 : ℝ) < (encloseK (nodes.getD i K.zero)).lo := by exact_mod_cast hb.1
  have hu : ((encloseK (nodes.getD i K.zero)).hi : ℝ) < 1 := by exact_mod_cast hb.2
  exact ⟨hl.trans_le h.1,h.2.trans_lt hu⟩

end Thomson8
