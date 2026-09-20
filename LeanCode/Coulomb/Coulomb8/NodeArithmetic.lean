import Coulomb8.ParameterBounds

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8
namespace NodeArithmetic
open Thomson8

def b0 : Box := ⟨(13359884191254877142271052110088134713/42535295865117307932921825928971026432),(106879073530039017138168450908941769799/340282366920938463463374607431768211456)⟩
noncomputable def v0 : ℝ := a
theorem h0 : b0.Contains v0 := by
  apply Box.contains_widen (parameterBox_contains)
  all_goals decide +kernel

def b1 : Box := ⟨2,2⟩
noncomputable def v1 : ℝ := ((2 : ℚ) : ℝ)
theorem h1 : b1.Contains v1 := by
  apply Box.contains_widen (Box.contains_rational (2))
  all_goals decide +kernel

def b2 : Box := ⟨(240615969168004511545033772477625056927/170141183460469231731687303715884105728),(481231938336009023090067544955250113855/340282366920938463463374607431768211456)⟩
noncomputable def v2 : ℝ := Real.sqrt v1
theorem h2 : b2.Contains v2 := by
  apply Box.contains_sqrt_interval h1 <;> decide +kernel

def b3 : Box := ⟨(13359884191254877142271052110088134713/21267647932558653966460912964485513216),(106879073530039017138168450908941769799/170141183460469231731687303715884105728)⟩
noncomputable def v3 : ℝ := v0 * v1
theorem h3 : b3.Contains v3 := by
  apply Box.contains_widen (Box.contains_times h0 h1)
  all_goals decide +kernel

def b4 : Box := ⟨1,1⟩
noncomputable def v4 : ℝ := ((1 : ℚ) : ℝ)
theorem h4 : b4.Contains v4 := by
  apply Box.contains_widen (Box.contains_rational (1))
  all_goals decide +kernel

def b5 : Box := ⟨-1,-1⟩
noncomputable def v5 : ℝ := -v4
theorem h5 : b5.Contains v5 := by
  apply Box.contains_widen (Box.contains_neg h4)
  all_goals decide +kernel

def b6 : Box := ⟨(-7907763741303776824189860854397378503/21267647932558653966460912964485513216),(-63262109930430214593518852806942335929/170141183460469231731687303715884105728)⟩
noncomputable def v6 : ℝ := v3 + v5
theorem h6 : b6.Contains v6 := by
  apply Box.contains_widen (Box.contains_add h3 h5)
  all_goals decide +kernel

def b7 : Box := ⟨(-106879073530039017138168450908941769799/340282366920938463463374607431768211456),(-13359884191254877142271052110088134713/42535295865117307932921825928971026432)⟩
noncomputable def v7 : ℝ := -v0
theorem h7 : b7.Contains v7 := by
  apply Box.contains_widen (Box.contains_neg h0)
  all_goals decide +kernel

def b8 : Box := ⟨(233403293390899446325206156522826441657/340282366920938463463374607431768211456),(29175411673862430790650773818882891719/42535295865117307932921825928971026432)⟩
noncomputable def v8 : ℝ := v4 + v7
theorem h8 : b8.Contains v8 := by
  apply Box.contains_widen (Box.contains_add h4 h7)
  all_goals decide +kernel

def b9 : Box := ⟨(120307984584002255772516886238812528463/170141183460469231731687303715884105728),(7519249036500140985782305389925783029/10633823966279326983230456482242756608)⟩
noncomputable def v9 : ℝ := v2⁻¹
theorem h9 : b9.Contains v9 := by
  apply Box.contains_widen (Box.contains_signedInverse (by decide +kernel) h2)
  all_goals decide +kernel

def b10 : Box := ⟨(41260262876994572188693763649405520429/85070591730234615865843651857942052864),(165041051507978288754775078659218998519/340282366920938463463374607431768211456)⟩
noncomputable def v10 : ℝ := v8 * v9
theorem h10 : b10.Contains v10 := by
  apply Box.contains_widen (Box.contains_times h8 h9)
  all_goals decide +kernel

def b11 : Box := ⟨(58161977977939271616606603688680311917/340282366920938463463374607431768211456),(58161977977939271616606661778513920815/340282366920938463463374607431768211456)⟩
noncomputable def v11 : ℝ := v7 + v10
theorem h11 : b11.Contains v11 := by
  apply Box.contains_widen (Box.contains_add h7 h10)
  all_goals decide +kernel

def b12 : Box := ⟨(-165041051507978288754775078659218998519/340282366920938463463374607431768211456),(-41260262876994572188693763649405520429/85070591730234615865843651857942052864)⟩
noncomputable def v12 : ℝ := -v10
theorem h12 : b12.Contains v12 := by
  apply Box.contains_widen (Box.contains_neg h10)
  all_goals decide +kernel

def b13 : Box := ⟨(-135960062519008652946471764784080384159/170141183460469231731687303715884105728),(-67980031259504326473235867869581789855/85070591730234615865843651857942052864)⟩
noncomputable def v13 : ℝ := v7 + v12
theorem h13 : b13.Contains v13 := by
  apply Box.contains_widen (Box.contains_add h7 h12)
  all_goals decide +kernel

end NodeArithmetic
end Coulomb8
