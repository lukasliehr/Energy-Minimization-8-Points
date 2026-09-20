import Coulomb8.BlockMatrix
import Coulomb8.FinitePositivity

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.PSDBounds.S7_even

def preconditioner : Matrix (Fin 8) (Fin 8) ℤ := ![![180593565927,0,0,0,0,0,0,0],![-297694864565,475302811157,0,0,0,0,0,0],![-268741422589,-142222643460,236033868876,0,0,0,0,0],![-4634612375166,9263967605461,-2559503089903,1293398453522,0,0,0,0],![-7138313392197,-547103366211,-1293234444674,4502034923553,8323176829472,0,0,0],![-3421973548291,-6069039919111,11960579549011,-5572043871850,-4665189594887,2317034359165,0,0],![723135635402,15810656608941,-7725696267763,334451695004,15030608188789,1147538683509,42251860416676,0],![-39571721355606,23862169222134,-29777490823040,39384795173318,45626478995726,-38263988167350,27177084100097,31363488814446]]
def boxes : Fin 8 → Fin 8 → Dyadic := ![![⟨12613469202219491488144137081958806061056,12613469202221967368222707842508604309504⟩,⟨7900153160696717196172491410725048156160,7900153160699193076251062171274846404608⟩,⟨19121587698112503436330521848257678671872,19121587698114979316409092608807476920320⟩,⟨26452436372959953305105405441604180770816,26452436372962429185183976202153979019264⟩,⟨-1237940039285380274899124224,1237940039285380274899124224⟩,⟨4228753899818303946324063869603342712832,4228753899820779826402634630153140961280⟩,⟨-1237940039285380274899124224,1237940039285380274899124224⟩,⟨-1237940039285380274899124224,1237940039285380274899124224⟩],![⟨7900153160696717196172491410725048156160,7900153160699193076251062171274846404608⟩,⟨6769028551851742015210203048173916651520,6769028551854217895288773808723714899968⟩,⟨13073579431923686036732881214483594215424,13073579431926161916811451975033392463872⟩,⟨5696584305877894591637277218905759154176,5696584305880370471715847979455557402624⟩,⟨6170493576294919342284223044036088299520,6170493576297395222362793804585886547968⟩,⟨-11965220514980872110181060414555998388224,-11965220514978396230102489654006200139776⟩,⟨-2192900234542037295161133679152971382784,-2192900234539561415082562918603173134336⟩,⟨-11597554709554938397358271085203626655744,-11597554709552462517279700324653828407296⟩],![⟨19121587698112503436330521848257678671872,19121587698114979316409092608807476920320⟩,⟨13073579431923686036732881214483594215424,13073579431926161916811451975033392463872⟩,⟨37032782030614428510845105914189271007232,37032782030616904390923676674739069255680⟩,⟨48162614157428707914746035295464040955904,48162614157431183794824606056013839204352⟩,⟨-3038409167467489881520741799213498630144,-3038409167465014001442171038663700381696⟩,⟨-18975311361719941269095215430664626110464,-18975311361717465389016644670114827862016⟩,⟨2766993496612469701026639452584380727296,2766993496614945581105210213134178975744⟩,⟨-32268705478430960918584829835015920549888,-32268705478428485038506259074466122301440⟩],![⟨26452436372959953305105405441604180770816,26452436372962429185183976202153979019264⟩,⟨5696584305877894591637277218905759154176,5696584305880370471715847979455557402624⟩,⟨48162614157428707914746035295464040955904,48162614157431183794824606056013839204352⟩,⟨149539559169181196630184810445787176632320,149539559169183672510263381206336974880768⟩,⟨-50341879498197938470958950958544147447808,-50341879498195462590880380197994349199360⟩,⟨63627079354888511604356036678639939485696,63627079354890987484434607439189737734144⟩,⟨21218830466247893848438606426039918788608,21218830466250369728517177186589717037056⟩,⟨19458774441348106221336203983702821175296,19458774441350582101414774744252619423744⟩],![⟨-1237940039285380274899124224,1237940039285380274899124224⟩,⟨6170493576294919342284223044036088299520,6170493576297395222362793804585886547968⟩,⟨-3038409167467489881520741799213498630144,-3038409167465014001442171038663700381696⟩,⟨-50341879498197938470958950958544147447808,-50341879498195462590880380197994349199360⟩,⟨27169535387886265006858625506544709533696,27169535387888740886937196267094507782144⟩,⟨-34512229248769977425714265665327494856704,-34512229248767501545635694904777696608256⟩,⟨-11193991762378242328737090666787973890048,-11193991762375766448658519906238175641600⟩,⟨-16293425298138908011379980408989237116928,-16293425298136432131301409648439438868480⟩],![⟨4228753899818303946324063869603342712832,4228753899820779826402634630153140961280⟩,⟨-11965220514980872110181060414555998388224,-11965220514978396230102489654006200139776⟩,⟨-18975311361719941269095215430664626110464,-18975311361717465389016644670114827862016⟩,⟨63627079354888511604356036678639939485696,63627079354890987484434607439189737734144⟩,⟨-34512229248769977425714265665327494856704,-34512229248767501545635694904777696608256⟩,⟨156455743388848361696493449283269606506496,156455743388850837576572020043819404754944⟩,⟨8459819939479128492273499405217748221952,8459819939481604372352070165767546470400⟩,⟨150278482935506175488143994510903345152000,150278482935508651368222565271453143400448⟩],![⟨-1237940039285380274899124224,1237940039285380274899124224⟩,⟨-2192900234542037295161133679152971382784,-2192900234539561415082562918603173134336⟩,⟨2766993496612469701026639452584380727296,2766993496614945581105210213134178975744⟩,⟨21218830466247893848438606426039918788608,21218830466250369728517177186589717037056⟩,⟨-11193991762378242328737090666787973890048,-11193991762375766448658519906238175641600⟩,⟨8459819939479128492273499405217748221952,8459819939481604372352070165767546470400⟩,⟨4911162205669458746501848048813503152128,4911162205671934626580418809363301400576⟩,⟨-1237940039285380274899124224,1237940039285380274899124224⟩],![⟨-1237940039285380274899124224,1237940039285380274899124224⟩,⟨-11597554709554938397358271085203626655744,-11597554709552462517279700324653828407296⟩,⟨-32268705478430960918584829835015920549888,-32268705478428485038506259074466122301440⟩,⟨19458774441348106221336203983702821175296,19458774441350582101414774744252619423744⟩,⟨-16293425298138908011379980408989237116928,-16293425298136432131301409648439438868480⟩,⟨150278482935506175488143994510903345152000,150278482935508651368222565271453143400448⟩,⟨-1237940039285380274899124224,1237940039285380274899124224⟩,⟨160797185297693477864685772403523213852672,160797185297695953744764343164073012101120⟩]]

theorem contains (w : Fin 192 → ℝ)
    (h : ∀ c, |w c-Witness.center c| ≤ (correctionRadius : ℝ))
    (i j : Fin 8) : (boxes i j).Contains (Data.S7_even.matrixFrom w i j) := by
  fin_cases i <;> fin_cases j
  · exact centerBox_contains w h 150
  · exact centerBox_contains w h 151
  · exact centerBox_contains w h 152
  · exact centerBox_contains w h 153
  · exact centerBox_contains w h 154
  · exact centerBox_contains w h 155
  · exact centerBox_contains w h 156
  · exact centerBox_contains w h 157
  · exact centerBox_contains w h 151
  · exact centerBox_contains w h 158
  · exact centerBox_contains w h 159
  · exact centerBox_contains w h 160
  · exact centerBox_contains w h 161
  · exact centerBox_contains w h 162
  · exact centerBox_contains w h 163
  · exact centerBox_contains w h 164
  · exact centerBox_contains w h 152
  · exact centerBox_contains w h 159
  · exact centerBox_contains w h 165
  · exact centerBox_contains w h 166
  · exact centerBox_contains w h 167
  · exact centerBox_contains w h 168
  · exact centerBox_contains w h 169
  · exact centerBox_contains w h 170
  · exact centerBox_contains w h 153
  · exact centerBox_contains w h 160
  · exact centerBox_contains w h 166
  · exact centerBox_contains w h 171
  · exact centerBox_contains w h 172
  · exact centerBox_contains w h 173
  · exact centerBox_contains w h 174
  · exact centerBox_contains w h 175
  · exact centerBox_contains w h 154
  · exact centerBox_contains w h 161
  · exact centerBox_contains w h 167
  · exact centerBox_contains w h 172
  · exact centerBox_contains w h 176
  · exact centerBox_contains w h 177
  · exact centerBox_contains w h 178
  · exact centerBox_contains w h 179
  · exact centerBox_contains w h 155
  · exact centerBox_contains w h 162
  · exact centerBox_contains w h 168
  · exact centerBox_contains w h 173
  · exact centerBox_contains w h 177
  · exact centerBox_contains w h 180
  · exact centerBox_contains w h 181
  · exact centerBox_contains w h 182
  · exact centerBox_contains w h 156
  · exact centerBox_contains w h 163
  · exact centerBox_contains w h 169
  · exact centerBox_contains w h 174
  · exact centerBox_contains w h 178
  · exact centerBox_contains w h 181
  · exact centerBox_contains w h 183
  · exact centerBox_contains w h 184
  · exact centerBox_contains w h 157
  · exact centerBox_contains w h 164
  · exact centerBox_contains w h 170
  · exact centerBox_contains w h 175
  · exact centerBox_contains w h 179
  · exact centerBox_contains w h 182
  · exact centerBox_contains w h 184
  · exact centerBox_contains w h 185

theorem checked0_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 8) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked0_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 8) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked0_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 8) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem checked0_3 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 3 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 8) 3) (2^80) ≤ 2^203 := by decide +kernel

theorem checked0_4 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 4 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 8) 4) (2^80) ≤ 2^203 := by decide +kernel

theorem checked0_5 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 5 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 8) 5) (2^80) ≤ 2^203 := by decide +kernel

theorem checked0_6 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 6 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 8) 6) (2^80) ≤ 2^203 := by decide +kernel

theorem checked0_7 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 7 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 8) 7) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 8) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 8) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 8) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_3 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 3 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 8) 3) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_4 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 4 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 8) 4) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_5 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 5 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 8) 5) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_6 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 6 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 8) 6) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_7 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 7 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 8) 7) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 8) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 8) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 8) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_3 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 3 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 8) 3) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_4 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 4 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 8) 4) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_5 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 5 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 8) 5) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_6 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 6 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 8) 6) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_7 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 7 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 8) 7) (2^80) ≤ 2^203 := by decide +kernel

theorem checked3_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 3 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (3 : Fin 8) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked3_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 3 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (3 : Fin 8) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked3_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 3 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (3 : Fin 8) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem checked3_3 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 3 k*preconditioner 3 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (3 : Fin 8) 3) (2^80) ≤ 2^203 := by decide +kernel

theorem checked3_4 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 3 k*preconditioner 4 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (3 : Fin 8) 4) (2^80) ≤ 2^203 := by decide +kernel

theorem checked3_5 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 3 k*preconditioner 5 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (3 : Fin 8) 5) (2^80) ≤ 2^203 := by decide +kernel

theorem checked3_6 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 3 k*preconditioner 6 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (3 : Fin 8) 6) (2^80) ≤ 2^203 := by decide +kernel

theorem checked3_7 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 3 k*preconditioner 7 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (3 : Fin 8) 7) (2^80) ≤ 2^203 := by decide +kernel

theorem checked4_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 4 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (4 : Fin 8) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked4_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 4 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (4 : Fin 8) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked4_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 4 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (4 : Fin 8) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem checked4_3 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 4 k*preconditioner 3 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (4 : Fin 8) 3) (2^80) ≤ 2^203 := by decide +kernel

theorem checked4_4 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 4 k*preconditioner 4 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (4 : Fin 8) 4) (2^80) ≤ 2^203 := by decide +kernel

theorem checked4_5 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 4 k*preconditioner 5 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (4 : Fin 8) 5) (2^80) ≤ 2^203 := by decide +kernel

theorem checked4_6 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 4 k*preconditioner 6 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (4 : Fin 8) 6) (2^80) ≤ 2^203 := by decide +kernel

theorem checked4_7 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 4 k*preconditioner 7 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (4 : Fin 8) 7) (2^80) ≤ 2^203 := by decide +kernel

theorem checked5_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 5 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (5 : Fin 8) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked5_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 5 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (5 : Fin 8) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked5_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 5 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (5 : Fin 8) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem checked5_3 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 5 k*preconditioner 3 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (5 : Fin 8) 3) (2^80) ≤ 2^203 := by decide +kernel

theorem checked5_4 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 5 k*preconditioner 4 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (5 : Fin 8) 4) (2^80) ≤ 2^203 := by decide +kernel

theorem checked5_5 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 5 k*preconditioner 5 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (5 : Fin 8) 5) (2^80) ≤ 2^203 := by decide +kernel

theorem checked5_6 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 5 k*preconditioner 6 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (5 : Fin 8) 6) (2^80) ≤ 2^203 := by decide +kernel

theorem checked5_7 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 5 k*preconditioner 7 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (5 : Fin 8) 7) (2^80) ≤ 2^203 := by decide +kernel

theorem checked6_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 6 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (6 : Fin 8) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked6_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 6 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (6 : Fin 8) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked6_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 6 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (6 : Fin 8) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem checked6_3 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 6 k*preconditioner 3 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (6 : Fin 8) 3) (2^80) ≤ 2^203 := by decide +kernel

theorem checked6_4 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 6 k*preconditioner 4 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (6 : Fin 8) 4) (2^80) ≤ 2^203 := by decide +kernel

theorem checked6_5 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 6 k*preconditioner 5 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (6 : Fin 8) 5) (2^80) ≤ 2^203 := by decide +kernel

theorem checked6_6 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 6 k*preconditioner 6 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (6 : Fin 8) 6) (2^80) ≤ 2^203 := by decide +kernel

theorem checked6_7 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 6 k*preconditioner 7 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (6 : Fin 8) 7) (2^80) ≤ 2^203 := by decide +kernel

theorem checked7_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 7 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (7 : Fin 8) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked7_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 7 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (7 : Fin 8) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked7_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 7 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (7 : Fin 8) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem checked7_3 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 7 k*preconditioner 3 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (7 : Fin 8) 3) (2^80) ≤ 2^203 := by decide +kernel

theorem checked7_4 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 7 k*preconditioner 4 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (7 : Fin 8) 4) (2^80) ≤ 2^203 := by decide +kernel

theorem checked7_5 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 7 k*preconditioner 5 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (7 : Fin 8) 5) (2^80) ≤ 2^203 := by decide +kernel

theorem checked7_6 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 7 k*preconditioner 6 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (7 : Fin 8) 6) (2^80) ≤ 2^203 := by decide +kernel

theorem checked7_7 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 7 k*preconditioner 7 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (7 : Fin 8) 7) (2^80) ≤ 2^203 := by decide +kernel

theorem positive (w : Fin 192 → ℝ)
    (h : ∀ c, |w c-Witness.center c| ≤ (correctionRadius : ℝ)) :
    (Data.S7_even.matrixFrom w).PosDef := by
  apply posDef_of_entry_bounds (Dyadic.scaledMatrix preconditioner) _ (by decide)
    (Data.S7_even.matrixFrom_symm w)
  intro i j
  apply Dyadic.congruence_entry_bound _ _ boxes (contains w h)
  fin_cases i <;> fin_cases j
  · exact checked0_0
  · exact checked0_1
  · exact checked0_2
  · exact checked0_3
  · exact checked0_4
  · exact checked0_5
  · exact checked0_6
  · exact checked0_7
  · exact checked1_0
  · exact checked1_1
  · exact checked1_2
  · exact checked1_3
  · exact checked1_4
  · exact checked1_5
  · exact checked1_6
  · exact checked1_7
  · exact checked2_0
  · exact checked2_1
  · exact checked2_2
  · exact checked2_3
  · exact checked2_4
  · exact checked2_5
  · exact checked2_6
  · exact checked2_7
  · exact checked3_0
  · exact checked3_1
  · exact checked3_2
  · exact checked3_3
  · exact checked3_4
  · exact checked3_5
  · exact checked3_6
  · exact checked3_7
  · exact checked4_0
  · exact checked4_1
  · exact checked4_2
  · exact checked4_3
  · exact checked4_4
  · exact checked4_5
  · exact checked4_6
  · exact checked4_7
  · exact checked5_0
  · exact checked5_1
  · exact checked5_2
  · exact checked5_3
  · exact checked5_4
  · exact checked5_5
  · exact checked5_6
  · exact checked5_7
  · exact checked6_0
  · exact checked6_1
  · exact checked6_2
  · exact checked6_3
  · exact checked6_4
  · exact checked6_5
  · exact checked6_6
  · exact checked6_7
  · exact checked7_0
  · exact checked7_1
  · exact checked7_2
  · exact checked7_3
  · exact checked7_4
  · exact checked7_5
  · exact checked7_6
  · exact checked7_7

end Coulomb8.PSDBounds.S7_even

#print axioms Coulomb8.PSDBounds.S7_even.positive
