import Coulomb8.BlockMatrix
import Coulomb8.FinitePositivity

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.PSDBounds.F1

def preconditioner : Matrix (Fin 5) (Fin 5) ℤ := ![![3909963732266,0,0,0,0],![-139916513171,4326999193006,0,0,0],![2412296352031,-2758374400565,4058508946955,0,0],![-2351332427062,3134148713643,-213498479458,2676820813436,0],![37108779876228,-64968383245232,12818302242208,-42970931761790,42618169897054]]
def boxes : Fin 5 → Fin 5 → Dyadic := ![![⟨26908757201198996932050308672130121728,26908757203674877010621069221928370176⟩,⟨870113283648578305549969641730736128,870113286124458384120730191528984576⟩,⟨-15402651429023412967274705190953943040,-15402651426547532888703944641155694592⟩,⟨21389525215629951757314844773769543680,21389525218105831835885605323567792128⟩,⟨4095492035530830395453511115347066880,4095492038006710474024271665145315328⟩],![⟨870113283648578305549969641730736128,870113286124458384120730191528984576⟩,⟨21999927241612580420372645402604732416,21999927244088460498943405952402980864⟩,⟨14435120330806207919101629835954356224,14435120333282087997672390385752604672⟩,⟨-23842926477460041846160427461382242304,-23842926474984161767589666911583993856⟩,⟨4397757120837334109001627379762724864,4397757123313214187572387929560973312⟩],![⟨-15402651429023412967274705190953943040,-15402651426547532888703944641155694592⟩,⟨14435120330806207919101629835954356224,14435120333282087997672390385752604672⟩,⟨43940921713435278150326240472431853568,43940921715911158228897001022230102016⟩,⟨-26926437232677836695465716469188263936,-26926437230201956616894955919390015488⟩,⟨-4948642362991951203384379573213855744,-4948642360516071124813619023415607296⟩],![⟨21389525215629951757314844773769543680,21389525218105831835885605323567792128⟩,⟨-23842926477460041846160427461382242304,-23842926474984161767589666911583993856⟩,⟨-26926437232677836695465716469188263936,-26926437230201956616894955919390015488⟩,⟨101969198790705418183783468207439872000,101969198793181298262354228757238120448⟩,⟨55940626535881894405163243539286458368,55940626538357774483734004089084706816⟩],![⟨4095492035530830395453511115347066880,4095492038006710474024271665145315328⟩,⟨4397757120837334109001627379762724864,4397757123313214187572387929560973312⟩,⟨-4948642362991951203384379573213855744,-4948642360516071124813619023415607296⟩,⟨55940626535881894405163243539286458368,55940626538357774483734004089084706816⟩,⟨61256574434058869322425097800290140160,61256574436534749400995858350088388608⟩]]

theorem contains (w : Fin 192 → ℝ)
    (h : ∀ c, |w c-Witness.center c| ≤ (correctionRadius : ℝ))
    (i j : Fin 5) : (boxes i j).Contains (Data.F1.matrixFrom w i j) := by
  fin_cases i <;> fin_cases j
  · exact centerBox_contains w h 10
  · exact centerBox_contains w h 11
  · exact centerBox_contains w h 12
  · exact centerBox_contains w h 13
  · exact centerBox_contains w h 14
  · exact centerBox_contains w h 11
  · exact centerBox_contains w h 15
  · exact centerBox_contains w h 16
  · exact centerBox_contains w h 17
  · exact centerBox_contains w h 18
  · exact centerBox_contains w h 12
  · exact centerBox_contains w h 16
  · exact centerBox_contains w h 19
  · exact centerBox_contains w h 20
  · exact centerBox_contains w h 21
  · exact centerBox_contains w h 13
  · exact centerBox_contains w h 17
  · exact centerBox_contains w h 20
  · exact centerBox_contains w h 22
  · exact centerBox_contains w h 23
  · exact centerBox_contains w h 14
  · exact centerBox_contains w h 18
  · exact centerBox_contains w h 21
  · exact centerBox_contains w h 23
  · exact centerBox_contains w h 24

theorem checked0_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 5) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked0_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 5) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked0_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 5) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem checked0_3 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 3 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 5) 3) (2^80) ≤ 2^203 := by decide +kernel

theorem checked0_4 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 4 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 5) 4) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 5) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 5) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 5) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_3 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 3 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 5) 3) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_4 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 4 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 5) 4) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 5) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 5) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 5) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_3 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 3 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 5) 3) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_4 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 4 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 5) 4) (2^80) ≤ 2^203 := by decide +kernel

theorem checked3_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 3 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (3 : Fin 5) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked3_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 3 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (3 : Fin 5) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked3_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 3 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (3 : Fin 5) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem checked3_3 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 3 k*preconditioner 3 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (3 : Fin 5) 3) (2^80) ≤ 2^203 := by decide +kernel

theorem checked3_4 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 3 k*preconditioner 4 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (3 : Fin 5) 4) (2^80) ≤ 2^203 := by decide +kernel

theorem checked4_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 4 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (4 : Fin 5) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked4_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 4 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (4 : Fin 5) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked4_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 4 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (4 : Fin 5) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem checked4_3 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 4 k*preconditioner 3 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (4 : Fin 5) 3) (2^80) ≤ 2^203 := by decide +kernel

theorem checked4_4 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 4 k*preconditioner 4 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (4 : Fin 5) 4) (2^80) ≤ 2^203 := by decide +kernel

theorem positive (w : Fin 192 → ℝ)
    (h : ∀ c, |w c-Witness.center c| ≤ (correctionRadius : ℝ)) :
    (Data.F1.matrixFrom w).PosDef := by
  apply posDef_of_entry_bounds (Dyadic.scaledMatrix preconditioner) _ (by decide)
    (Data.F1.matrixFrom_symm w)
  intro i j
  apply Dyadic.congruence_entry_bound _ _ boxes (contains w h)
  fin_cases i <;> fin_cases j
  · exact checked0_0
  · exact checked0_1
  · exact checked0_2
  · exact checked0_3
  · exact checked0_4
  · exact checked1_0
  · exact checked1_1
  · exact checked1_2
  · exact checked1_3
  · exact checked1_4
  · exact checked2_0
  · exact checked2_1
  · exact checked2_2
  · exact checked2_3
  · exact checked2_4
  · exact checked3_0
  · exact checked3_1
  · exact checked3_2
  · exact checked3_3
  · exact checked3_4
  · exact checked4_0
  · exact checked4_1
  · exact checked4_2
  · exact checked4_3
  · exact checked4_4

end Coulomb8.PSDBounds.F1

#print axioms Coulomb8.PSDBounds.F1.positive
