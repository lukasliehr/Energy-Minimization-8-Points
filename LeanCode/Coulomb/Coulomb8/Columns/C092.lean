import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C092

def r0 : ℚ := { num := 32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -983040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 11894784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -70123520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 141819904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 826540032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -8217231360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 2327314432, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -143059025920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 24923406336, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -984514068480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 1648358195200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -1809954963456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 163715874816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -332726796288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := 34426847232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := -1179648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 16875520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -123469824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 27262976, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -24117248, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -4987617280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := 34631319552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := -148405714944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := 490647977984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -1208121589760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := 2039146610688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := -2134757408768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 1160944287744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -27773632512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 1638400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -14286848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 4849664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 263651328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -2405171200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 9599975424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -26392657920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 56434163712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -9724297216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -64414679040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 55947689984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -79041986560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 38232784896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 131072, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -27394048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 146014208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -193265664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -1706295296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 99876864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -47925166080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 154012549120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -21271281664, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 74348888064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -364515688448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 62647762944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -65536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -1277952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 50593792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -302972928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 593887232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 1028456448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -10726146048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 47326330880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -132405198848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 199832797184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -17434148864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := -1048576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := 10518528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -4194304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -123142144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 1011875840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -3475177472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 10928259072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -25752600576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 547356672, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -612794368, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := -196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := 524288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := -19136512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -1572864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 47316992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -235405312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 6073090048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -14334558208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 13621854208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 10289152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -106823680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 574750720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := -1774714880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 3333816320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -917766144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -41304457216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := 37665767424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -49562714112, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 1511227785216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -207532457984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 12004884480, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 2031616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -24051712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 135135232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -331022336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -27918336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 4644012032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -3333947392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 11136598016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := -159367888896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 21938241536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 4673634304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -12464357376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 589824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -13434880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 112459776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -428081152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 689831936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := 57016320, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := -9678094336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := 8215855104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := -170890559488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := 245645377536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := -19845349376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -851968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 7700480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -3932160, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 15532032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := 236584960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := -1578958848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 4977328128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -2363850752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -2558722048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 29327360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -25427968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 90701824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -220332032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 21495808, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := 232521728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := -2347237376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 22740992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := 65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := -1310720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := 6356992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 2097152, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -493748224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 2236088320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -6216351744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 13842251776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := -20345716736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := 4796973056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 186843136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -273678336, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := -1900544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := 19005440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := -10223616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 44695552, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -3285712896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := 707526656, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := -28776005632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := 3955032064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := -273547264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 1048576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -38273024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := -3145728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := 94633984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := -470810624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := 12146180096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -28669116416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 27243708416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 983040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := -18087936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := 134086656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -45613056, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 306315264, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -26414678016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := 69838307328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := -2716336128, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := -197690720256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := 68555636736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := -399900672, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := 2097152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -24576000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 121765888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -130678784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := -938999808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 154271744, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 1511784448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -9351528448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 663224320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := 10122231808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 1966080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := 262144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := -65536, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 74448896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := 10616832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := -1440219136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := 3162898432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 2465202176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -13644922880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 6029312, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -1441792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := 1310720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 8388608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -300548096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 1022623744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -424935424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -3209691136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 637992960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := -917504, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := 11272192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -524288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -308936704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := 162004992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := -473169920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -3690463232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := 39256064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 1966080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := -20512768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 63438848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := 371064832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -3597402112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 10479861760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := -6542589952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -27761901568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 8490450944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -42795008, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := -196608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := 6553600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 36438016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -379715584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := 749338624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 1255407616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := -4509138944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -127336448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := 47513600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := 131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 24641536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -42991616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -322174976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 1462763520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -856162304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -4251975680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 47054848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := 1572864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -84934656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -26476544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := 657457152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := -765984768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := -9437184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := 786432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := -18874368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := 9437184, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := -509607936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := -158859264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 3944742912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -4595908608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := -56623104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := 16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := -491520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := 5947392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := -35061760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := 70909952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := 413270016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := -4108615680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := 1163657216, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -71529512960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := 12461703168, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := -492257034240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 824179097600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := -904977481728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := 81857937408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := -166363398144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := 17213423616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := -589824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := 8437760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := -61734912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := 13631488, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := -12058624, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := -2493808640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := 17315659776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := -74202857472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := 245323988992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := -604060794880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := 1019573305344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := -1067378704384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := 580472143872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := -13886816256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := -32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := 819200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := -7143424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := 2424832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 131825664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -1202585600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 4799987712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -13196328960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := 28217081856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := -4862148608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -32207339520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := 27973844992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := -39520993280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := 19116392448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := 65536, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -13697024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 73007104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := -96632832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -853147648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 49938432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -23962583040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 77006274560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -10635640832, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 37174444032, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -182257844224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 31323881472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -32768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := -638976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := 25296896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := -151486464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 296943616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := 514228224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := -5363073024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := 23663165440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := -66202599424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := 99916398592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := -8717074432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := 5259264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := -2097152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -61571072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 505937920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := -1737588736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 5464129536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -12876300288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 273678336, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -306397184, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := -98304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -9568256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := -786432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := 23658496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := -117702656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := 3036545024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := -7167279104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := 6810927104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := 5144576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := -53411840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := 287375360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := -887357440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := 1666908160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := -458883072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := -20652228608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := 18832883712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := -24781357056, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := 755613892608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := -103766228992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := 6002442240, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := 1015808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := -12025856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := 67567616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := -165511168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -13959168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 2322006016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := -1666973696, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := 5568299008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := -79683944448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := 10969120768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := 2336817152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := -6232178688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := 294912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -6717440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := 56229888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := -214040576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := 344915968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := 28508160, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := -4839047168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := 4107927552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := -85445279744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := 122822688768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -9922674688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := -425984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := 3850240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := -1966080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := 7766016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := 118292480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := -789479424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := 2488664064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := -1181925376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := -1279361024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := 14663680, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := -12713984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := 45350912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := -110166016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := 10747904, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := 116260864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := -1173618688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := 11370496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := -655360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := 3178496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := 1048576, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := -246874112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := 1118044160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := -3108175872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := 6921125888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := -10172858368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := 2398486528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := 93421568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := -136839168, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := -950272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := 9502720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := -5111808, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := 196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := 22347776, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := -1642856448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := 353763328, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := -14388002816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := 1977516032, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := -136773632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := 491520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := -9043968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := 67043328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := -22806528, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := 153157632, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := -13207339008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := 34919153664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := -1358168064, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := -98845360128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := 34277818368, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := -199950336, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := 1048576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := -12288000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := 60882944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := -65339392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := -469499904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := 77135872, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := 755892224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := -4675764224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := 331612160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := 5061115904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := 983040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := 131072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := -32768, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := 37224448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := 5308416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := -720109568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := 1581449216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := 1232601088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := -6822461440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := 3014656, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := -720896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := 655360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := 4194304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := -150274048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := 511311872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := -212467712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := -1604845568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := 318996480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := -458752, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r454 : ℚ := { num := 5636096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r455 : ℚ := { num := -262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r456 : ℚ := { num := -154468352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r457 : ℚ := { num := 81002496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r458 : ℚ := { num := -236584960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r459 : ℚ := { num := -1845231616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r460 : ℚ := { num := 19628032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r461 : ℚ := { num := -10256384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r462 : ℚ := { num := 31719424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r463 : ℚ := { num := 185532416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r464 : ℚ := { num := -1798701056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r465 : ℚ := { num := 5239930880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r466 : ℚ := { num := -3271294976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r467 : ℚ := { num := -13880950784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r468 : ℚ := { num := 4245225472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r469 : ℚ := { num := -21397504, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r470 : ℚ := { num := -98304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r471 : ℚ := { num := 3276800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r472 : ℚ := { num := 18219008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r473 : ℚ := { num := -189857792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r474 : ℚ := { num := 374669312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r475 : ℚ := { num := 627703808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r476 : ℚ := { num := -2254569472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r477 : ℚ := { num := -63668224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r478 : ℚ := { num := 23756800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r479 : ℚ := { num := 12320768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r480 : ℚ := { num := -21495808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r481 : ℚ := { num := -161087488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r482 : ℚ := { num := 731381760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r483 : ℚ := { num := -2125987840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r484 : ℚ := { num := 23527424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r485 : ℚ := { num := 786432, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r486 : ℚ := { num := -42467328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r487 : ℚ := { num := -13238272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r488 : ℚ := { num := 328728576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r489 : ℚ := { num := -382992384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r490 : ℚ := { num := -4718592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r491 : ℚ := { num := -9437184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r492 : ℚ := { num := 4718592, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r493 : ℚ := { num := -254803968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r494 : ℚ := { num := -79429632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r495 : ℚ := { num := 1972371456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r496 : ℚ := { num := -2297954304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r497 : ℚ := { num := -28311552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r498 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r499 : ℚ := { num := 1, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15],[r0,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29],[r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43],[r30,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55],[r0,r56,r57,r58,r59,r60,r61,r62,r63,r64,r65,r66],[r0,r67,r68,r69,r70,r71,r72,r73,r74,r75,r76],[0,r77,r78,r79,r80,r81,r82,r83,r84,r85],[],[],[],[],[],[],[0,r86,r87,r88,r89,r90,r91,r92,r93,r94,r95,r96,r97,r98],[r30,r99,r100,r101,r102,r103,r104,r105,r106,r107,r108,r109,r110],[0,r111,r112,r113,r114,r115,r116,r117,r118,r119,r120,r121],[r0,r122,r123,r124,r125,r126,r127,r128,r129,r130,r131],[0,r77,r78,r132,r133,r134,r135,r136,r137,r138],[],[],[],[],[],[],[r139,r140,r141,r142,r143,r144,r145,r146,r147,r148,r149,r150],[r139,r151,r152,r153,r154,r155,r156,r157,r158,r159,r160],[0,r77,r78,r132,r133,r134,r135,r136,r137,r138],[],[],[],[],[],[],[0,r86,r161,r162,r163,r164,r165,r166,r167,r168],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,0,r169,r170,r171,r172,r173,r174,r175,r176,r177,r178,r179],[r30,r180,r181,r182,r183,r184,r185,r186,r187,r188,r189,r190],[r30,r191,r192,r193,r194,r195,r196,r197,r198,r199,720896],[r139,r200,r201,r202,r203,r204,r205,r206,r207,r208],[r139,r80,r209,r210,r211,r212,r213,r214,r215],[],[],[],[],[],[r30,r216,r217,r218,r219,r220,r221,r222,r223,r224,r225],[r139,r226,r227,r228,r229,r230,r231,r232,r233,r234],[r235,r163,r236,r237,r238,r239,r240,r241,r242],[],[],[],[],[],[r235,r163,r243,r244,r245,r246,r247,r248,131072],[],[],[],[],[],[],[],[],[],[],[],[0,r249,r250,r251,r252,r253,r254,r255,r256,786432],[r235,r163,r243,r244,r245,r246,r247,r248,131072],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[r257,r258,r259,r260,r261,r262,r263,r264,r265,r266,r267,r268,r269,r270,r271,r272]),(⟨0,0,1⟩,[r257,r273,r274,r275,r276,r277,r278,r279,r280,r281,r282,r283,r284,r285,r286]),(⟨0,0,2⟩,[r287,r288,r289,r290,r291,r292,r293,r294,r295,r296,r297,r298,r299,r300]),(⟨0,0,3⟩,[r287,r301,r302,r303,r304,r305,r306,r307,r308,r309,r310,r311,r312]),(⟨0,0,4⟩,[r257,r313,r314,r315,r316,r317,r318,r319,r320,r321,r322,r323]),(⟨0,0,5⟩,[r257,r210,r324,r325,r326,r327,r328,r329,r330,r331,r332]),(⟨0,0,6⟩,[0,r333,r191,r334,r335,r336,r337,r338,r339,r340]),(⟨0,1,0⟩,[r257,r273,r274,r275,r276,r277,r278,r279,r280,r281,r282,r283,r284,r285,r286]),(⟨0,1,1⟩,[0,r77,r341,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351,r352]),(⟨0,1,2⟩,[r287,r353,r354,r355,r356,r357,r358,r359,r360,r361,r362,r363,r364]),(⟨0,1,3⟩,[0,r365,r366,r367,r368,r369,r370,r371,r372,r373,r374,r375]),(⟨0,1,4⟩,[r257,r376,r377,r378,r379,r380,r381,r382,r383,r384,r385]),(⟨0,1,5⟩,[0,r333,r191,r386,r387,r388,r389,r390,r391,r392]),(⟨0,2,0⟩,[r287,r288,r289,r290,r291,r292,r293,r294,r295,r296,r297,r298,r299,r300]),(⟨0,2,1⟩,[r287,r353,r354,r355,r356,r357,r358,r359,r360,r361,r362,r363,r364]),(⟨0,2,2⟩,[r0,r393,r394,r395,r396,r397,r398,r399,r400,r401,r402,r403]),(⟨0,2,3⟩,[r0,r404,r405,r406,r407,r408,r409,r410,r411,r412,r413]),(⟨0,2,4⟩,[0,r333,r191,r386,r387,r388,r389,r390,r391,r392]),(⟨0,3,0⟩,[r287,r301,r302,r303,r304,r305,r306,r307,r308,r309,r310,r311,r312]),(⟨0,3,1⟩,[0,r365,r366,r367,r368,r369,r370,r371,r372,r373,r374,r375]),(⟨0,3,2⟩,[r0,r404,r405,r406,r407,r408,r409,r410,r411,r412,r413]),(⟨0,3,3⟩,[0,r77,r78,r79,r80,r81,r82,r83,r84,r85]),(⟨0,4,0⟩,[r257,r313,r314,r315,r316,r317,r318,r319,r320,r321,r322,r323]),(⟨0,4,1⟩,[r257,r376,r377,r378,r379,r380,r381,r382,r383,r384,r385]),(⟨0,4,2⟩,[0,r333,r191,r386,r387,r388,r389,r390,r391,r392]),(⟨0,5,0⟩,[r257,r210,r324,r325,r326,r327,r328,r329,r330,r331,r332]),(⟨0,5,1⟩,[0,r333,r191,r386,r387,r388,r389,r390,r391,r392]),(⟨0,6,0⟩,[0,r333,r191,r334,r335,r336,r337,r338,r339,r340]),(⟨1,0,0⟩,[r257,r273,r274,r275,r276,r277,r278,r279,r280,r281,r282,r283,r284,r285,r286]),(⟨1,0,1⟩,[0,r77,r341,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351,r352]),(⟨1,0,2⟩,[r287,r353,r354,r355,r356,r357,r358,r359,r360,r361,r362,r363,r364]),(⟨1,0,3⟩,[0,r365,r366,r367,r368,r369,r370,r371,r372,r373,r374,r375]),(⟨1,0,4⟩,[r257,r376,r377,r378,r379,r380,r381,r382,r383,r384,r385]),(⟨1,0,5⟩,[0,r333,r191,r386,r387,r388,r389,r390,r391,r392]),(⟨1,1,0⟩,[0,r77,r341,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351,r352]),(⟨1,1,1⟩,[0,0,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423,r424]),(⟨1,1,2⟩,[r287,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434,r435]),(⟨1,1,3⟩,[r287,r436,r437,r438,r439,r440,r441,r442,r443,r444,360448]),(⟨1,1,4⟩,[r0,r445,r446,r447,r448,r449,r450,r451,r452,r453]),(⟨1,1,5⟩,[r0,r335,r454,r455,r456,r457,r458,r459,r460]),(⟨1,2,0⟩,[r287,r353,r354,r355,r356,r357,r358,r359,r360,r361,r362,r363,r364]),(⟨1,2,1⟩,[r287,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434,r435]),(⟨1,2,2⟩,[r287,r169,r461,r462,r463,r464,r465,r466,r467,r468,r469]),(⟨1,2,3⟩,[r0,r470,r471,r472,r473,r474,r475,r476,r477,r478]),(⟨1,2,4⟩,[r139,r80,r479,r480,r481,r482,r114,r483,r484]),(⟨1,3,0⟩,[0,r365,r366,r367,r368,r369,r370,r371,r372,r373,r374,r375]),(⟨1,3,1⟩,[r287,r436,r437,r438,r439,r440,r441,r442,r443,r444,360448]),(⟨1,3,2⟩,[r0,r470,r471,r472,r473,r474,r475,r476,r477,r478]),(⟨1,3,3⟩,[r139,r80,r485,r486,r487,r488,r489,r490,65536]),(⟨1,4,0⟩,[r257,r376,r377,r378,r379,r380,r381,r382,r383,r384,r385]),(⟨1,4,1⟩,[r0,r445,r446,r447,r448,r449,r450,r451,r452,r453]),(⟨1,4,2⟩,[r139,r80,r479,r480,r481,r482,r114,r483,r484]),(⟨1,5,0⟩,[0,r333,r191,r386,r387,r388,r389,r390,r391,r392]),(⟨1,5,1⟩,[r0,r335,r454,r455,r456,r457,r458,r459,r460]),(⟨2,0,0⟩,[r287,r288,r289,r290,r291,r292,r293,r294,r295,r296,r297,r298,r299,r300]),(⟨2,0,1⟩,[r287,r353,r354,r355,r356,r357,r358,r359,r360,r361,r362,r363,r364]),(⟨2,0,2⟩,[r0,r393,r394,r395,r396,r397,r398,r399,r400,r401,r402,r403]),(⟨2,0,3⟩,[r0,r404,r405,r406,r407,r408,r409,r410,r411,r412,r413]),(⟨2,0,4⟩,[0,r333,r191,r386,r387,r388,r389,r390,r391,r392]),(⟨2,1,0⟩,[r287,r353,r354,r355,r356,r357,r358,r359,r360,r361,r362,r363,r364]),(⟨2,1,1⟩,[r287,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434,r435]),(⟨2,1,2⟩,[r287,r169,r461,r462,r463,r464,r465,r466,r467,r468,r469]),(⟨2,1,3⟩,[r0,r470,r471,r472,r473,r474,r475,r476,r477,r478]),(⟨2,1,4⟩,[r139,r80,r479,r480,r481,r482,r114,r483,r484]),(⟨2,2,0⟩,[r0,r393,r394,r395,r396,r397,r398,r399,r400,r401,r402,r403]),(⟨2,2,1⟩,[r287,r169,r461,r462,r463,r464,r465,r466,r467,r468,r469]),(⟨2,2,2⟩,[0,r154,r491,r492,r493,r494,r495,r496,r497,393216]),(⟨2,2,3⟩,[r139,r80,r485,r486,r487,r488,r489,r490,65536]),(⟨2,3,0⟩,[r0,r404,r405,r406,r407,r408,r409,r410,r411,r412,r413]),(⟨2,3,1⟩,[r0,r470,r471,r472,r473,r474,r475,r476,r477,r478]),(⟨2,3,2⟩,[r139,r80,r485,r486,r487,r488,r489,r490,65536]),(⟨2,4,0⟩,[0,r333,r191,r386,r387,r388,r389,r390,r391,r392]),(⟨2,4,1⟩,[r139,r80,r479,r480,r481,r482,r114,r483,r484]),(⟨3,0,0⟩,[r287,r301,r302,r303,r304,r305,r306,r307,r308,r309,r310,r311,r312]),(⟨3,0,1⟩,[0,r365,r366,r367,r368,r369,r370,r371,r372,r373,r374,r375]),(⟨3,0,2⟩,[r0,r404,r405,r406,r407,r408,r409,r410,r411,r412,r413]),(⟨3,0,3⟩,[0,r77,r78,r79,r80,r81,r82,r83,r84,r85]),(⟨3,1,0⟩,[0,r365,r366,r367,r368,r369,r370,r371,r372,r373,r374,r375]),(⟨3,1,1⟩,[r287,r436,r437,r438,r439,r440,r441,r442,r443,r444,360448]),(⟨3,1,2⟩,[r0,r470,r471,r472,r473,r474,r475,r476,r477,r478]),(⟨3,1,3⟩,[r139,r80,r485,r486,r487,r488,r489,r490,65536]),(⟨3,2,0⟩,[r0,r404,r405,r406,r407,r408,r409,r410,r411,r412,r413]),(⟨3,2,1⟩,[r0,r470,r471,r472,r473,r474,r475,r476,r477,r478]),(⟨3,2,2⟩,[r139,r80,r485,r486,r487,r488,r489,r490,65536]),(⟨3,3,0⟩,[0,r77,r78,r79,r80,r81,r82,r83,r84,r85]),(⟨3,3,1⟩,[r139,r80,r485,r486,r487,r488,r489,r490,65536]),(⟨4,0,0⟩,[r257,r313,r314,r315,r316,r317,r318,r319,r320,r321,r322,r323]),(⟨4,0,1⟩,[r257,r376,r377,r378,r379,r380,r381,r382,r383,r384,r385]),(⟨4,0,2⟩,[0,r333,r191,r386,r387,r388,r389,r390,r391,r392]),(⟨4,1,0⟩,[r257,r376,r377,r378,r379,r380,r381,r382,r383,r384,r385]),(⟨4,1,1⟩,[r0,r445,r446,r447,r448,r449,r450,r451,r452,r453]),(⟨4,1,2⟩,[r139,r80,r479,r480,r481,r482,r114,r483,r484]),(⟨4,2,0⟩,[0,r333,r191,r386,r387,r388,r389,r390,r391,r392]),(⟨4,2,1⟩,[r139,r80,r479,r480,r481,r482,r114,r483,r484]),(⟨5,0,0⟩,[r257,r210,r324,r325,r326,r327,r328,r329,r330,r331,r332]),(⟨5,0,1⟩,[0,r333,r191,r386,r387,r388,r389,r390,r391,r392]),(⟨5,1,0⟩,[0,r333,r191,r386,r387,r388,r389,r390,r391,r392]),(⟨5,1,1⟩,[r0,r335,r454,r455,r456,r457,r458,r459,r460]),(⟨6,0,0⟩,[0,r333,r191,r334,r335,r336,r337,r338,r339,r340])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[128,-1792,5120,30720,-231808,574208,-567040,116736]),(⟨0,0,1⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨0,0,2⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨0,0,3⟩,[-128,1536,256,-37376,76672]),(⟨0,1,0⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨0,1,1⟩,[0,-512,6144,-15360,-18432,60928]),(⟨0,1,2⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨0,2,1⟩,[-128,1536,-3840,-4608,15232]),(⟨0,3,0⟩,[-128,1536,256,-37376,76672]),(⟨1,0,0⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨1,0,1⟩,[0,-512,6144,-15360,-18432,60928]),(⟨1,0,2⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[0,-512,6144,-15360,-18432,60928]),(⟨1,2,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨2,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨2,1,0⟩,[-128,1536,-3840,-4608,15232]),(⟨3,0,0⟩,[-128,1536,256,-37376,76672])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[128,-2048,12672,-45312,136064,-378368,739968,-708864,147456]),(⟨0,0,1⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨0,0,2⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨0,0,3⟩,[0,768,-5120,14848,-50176,88832]),(⟨0,1,0⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨0,1,1⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨0,2,0⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨0,3,0⟩,[0,768,-5120,14848,-50176,88832]),(⟨1,0,0⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨1,0,1⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨1,1,0⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨1,1,2⟩,[-256,3072,-7680,-9216,30464]),(⟨1,2,1⟩,[-256,3072,-7680,-9216,30464]),(⟨2,0,0⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨2,1,1⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[0,768,-5120,14848,-50176,88832])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 3 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r498) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 11 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r498) sourceRight))).isZero := by decide +kernel

noncomputable def partial19 : Poly := []

theorem partial_sound19 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 19)
      sourceRight).eval u v t=partial19.eval u v t := by rfl

noncomputable def chunk16 : Poly := [(⟨2,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨2,1,0⟩,[-128,1536,-3840,-4608,15232]),(⟨3,0,0⟩,[-128,1536,256,-37376,76672])]

noncomputable def partial16 : Poly := [(⟨2,0,1⟩,[-16384,458752,-5259264,32538624,-124289024,341835776,-796557312,1363083264,-133120000,-6224543744,13971406848,-11476893696,2246049792]),(⟨2,0,2⟩,[0,65536,-1441792,12615680,-60030976,193724416,-520617984,1016004608,-284950528,-4165533696,9175957504,-6305316864]),(⟨2,0,3⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨2,0,4⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨2,1,0⟩,[-16384,458752,-5259264,32538624,-124289024,341835776,-796557312,1363083264,-133120000,-6224543744,13971406848,-11476893696,2246049792]),(⟨2,1,1⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨2,1,2⟩,[16384,-425984,4243456,-21102592,61767680,-126025728,94732288,549847040,-1511702528,432373760,1187364864]),(⟨2,1,3⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨2,2,0⟩,[0,65536,-1441792,12615680,-60030976,193724416,-520617984,1016004608,-284950528,-4165533696,9175957504,-6305316864]),(⟨2,2,1⟩,[16384,-425984,4243456,-21102592,61767680,-126025728,94732288,549847040,-1511702528,432373760,1187364864]),(⟨2,3,0⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨2,3,1⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨2,4,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨3,0,0⟩,[-16384,458752,-4734976,19955712,2588672,-384827392,2024112128,-7429226496,23655923712,-56622252032,83267076096,-59861336064,11305746432]),(⟨3,0,1⟩,[0,131072,-2883584,23134208,-82313216,99090432,284164096,-2643591168,13501988864,-40007499776,61234479104,-38043844608]),(⟨3,0,2⟩,[16384,-425984,3719168,-9568256,-33652736,267190272,-924483584,3000369152,-6684327936,5764382720,361611264]),(⟨3,0,3⟩,[0,-98304,1835008,-9568256,-786432,165609472,-823918592,3036545024,-7167279104,6810927104]),(⟨3,1,0⟩,[0,131072,-2883584,23134208,-82313216,99090432,284164096,-2643591168,13501988864,-40007499776,61234479104,-38043844608]),(⟨3,1,1⟩,[0,0,294912,-7077888,57016320,-128188416,-503119872,2687238144,-1858732032,-7220232192,9791373312]),(⟨3,1,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,2,0⟩,[16384,-425984,3719168,-9568256,-33652736,267190272,-924483584,3000369152,-6684327936,5764382720,361611264]),(⟨3,2,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,3,0⟩,[0,-98304,1835008,-9568256,-786432,165609472,-823918592,3036545024,-7167279104,6810927104]),(⟨3,3,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,0,0⟩,[0,65536,-1441792,10518528,-22282240,-94633984,804782080,-3659595776,13786939392,-35841966080,52058521600,-31738527744]),(⟨4,0,1⟩,[16384,-425984,4243456,-21102592,58621952,-63111168,-348815360,1757806592,-1646968832,-4261052416,6802489344]),(⟨4,1,0⟩,[16384,-425984,4243456,-21102592,58621952,-63111168,-348815360,1757806592,-1646968832,-4261052416,6802489344]),(⟨4,1,2⟩,[65536,-1572864,12320768,-21495808,-161087488,731381760,-428081152,-2125987840,2799763456]),(⟨4,2,1⟩,[65536,-1572864,12320768,-21495808,-161087488,731381760,-428081152,-2125987840,2799763456]),(⟨5,0,0⟩,[16384,-425984,3620864,-7208960,-53706752,330891264,-904626176,2507276288,-6109839360,6606651392,-1030471680]),(⟨5,0,1⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨5,1,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨5,1,1⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨6,0,0⟩,[0,-98304,1835008,-9568256,-786432,165609472,-823918592,3036545024,-7167279104,6810927104])]


theorem partial_checked16 :
    (Poly.add (Poly.add (Poly.mul chunk16 sourceRight) partial19)
      (Poly.scale (K.ofRat (-1)) partial16)).isZero := by decide +kernel

theorem partial_sound16 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 16)
      sourceRight).eval u v t=partial16.eval u v t := by
  change (Poly.mul (chunk16++(sourceLeft.drop 19))
    sourceRight).eval u v t=partial16.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound19 partial_checked16 u v t


noncomputable def chunk12 : Poly := [(⟨1,0,2⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[0,-512,6144,-15360,-18432,60928]),(⟨1,2,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[-128,1280,1280,-34816,69504,-12544])]

noncomputable def partial12 : Poly := [(⟨1,0,2⟩,[-16384,458752,-5259264,32538624,-124289024,341835776,-796557312,1363083264,-133120000,-6224543744,13971406848,-11476893696,2246049792]),(⟨1,0,3⟩,[0,65536,-1441792,12615680,-60030976,193724416,-520617984,1016004608,-284950528,-4165533696,9175957504,-6305316864]),(⟨1,0,4⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨1,0,5⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨1,1,0⟩,[0,-65536,1835008,-21037056,130154496,-497156096,1367343104,-3186229248,5452333056,-532480000,-24898174976,55885627392,-45907574784,8984199168]),(⟨1,1,1⟩,[0,0,262144,-5767168,50462720,-240123904,774897664,-2082471936,4064018432,-1139802112,-16662134784,36703830016,-25221267456]),(⟨1,1,2⟩,[0,131072,-3145728,29196288,-135004160,360579072,-769916928,1474363392,-57933824,-7914389504,14274527232,-7124189184]),(⟨1,1,3⟩,[0,0,-294912,4980736,-30801920,117702656,-460521472,1223950336,-109445120,-5536743424,6804439040]),(⟨1,2,0⟩,[-16384,458752,-4997120,26771456,-73826304,101711872,-21659648,-719388672,3930898432,-7364345856,-2690727936,25226936320,-22975217664]),(⟨1,2,1⟩,[0,65536,-1441792,13008896,-69468160,273940480,-775421952,936574976,1687420928,-6463488000,5806882816,-736985088]),(⟨1,2,2⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨1,2,3⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨1,3,0⟩,[0,131072,-3145728,29196288,-135004160,360579072,-769916928,1474363392,-57933824,-7914389504,14274527232,-7124189184]),(⟨1,3,1⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨1,3,2⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨1,4,0⟩,[16384,-425984,3751936,-11403264,-9142272,119078912,-326074368,787611648,-472170496,-3419832320,5207638016]),(⟨1,5,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨2,0,0⟩,[-16384,425984,-4079616,14942208,21004288,-420544512,2079162368,-7491944448,23219585024,-54486204416,81045536768,-63684870144,19140771840,-1849688064]),(⟨2,0,1⟩,[-16384,524288,-6569984,41222144,-137068544,223084544,56459264,-2379874304,13402554368,-40507277312,64478429184,-46234009600,7438663680]),(⟨2,0,2⟩,[16384,-262144,147456,21331968,-178749440,712638464,-1947303936,4516282368,-6357565440,-1817313280,16419078144,-12442042368]),(⟨2,0,3⟩,[16384,-524288,5881856,-28573696,53903360,49020928,-738230272,3506700288,-8278163456,7235960832,73056256]),(⟨2,0,4⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨2,1,0⟩,[-16384,524288,-6307840,35454976,-86605824,-17039360,831356928,-4462346240,17466572800,-41647079424,47816294400,-9530179584,-17782603776]),(⟨2,1,1⟩,[0,131072,-2785280,23461888,-115736576,480247808,-1746862080,3486515200,765067264,-15443558400,21681766400,-8188723200]),(⟨2,1,2⟩,[16384,-425984,4341760,-23461888,81821696,-189726720,74874880,1042939904,-2086191104,-409894912,2579447808]),(⟨2,1,3⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨2,1,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,2,0⟩,[16384,-262144,147456,21725184,-188186624,792854528,-2202107904,4436852736,-4385193984,-4115267584,13050003456,-6873710592]),(⟨2,2,1⟩,[16384,-425984,4341760,-23461888,81821696,-189726720,74874880,1042939904,-2086191104,-409894912,2579447808]),(⟨2,2,2⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,2,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,3,0⟩,[16384,-524288,5881856,-28573696,53903360,49020928,-738230272,3506700288,-8278163456,7235960832,73056256]),(⟨2,3,1⟩,[0,32768,-1310720,14024704,-39583744,-136642560,840171520,-649723904,-2296643584,3209199616]),(⟨2,3,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,4,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨2,4,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,0,0⟩,[-16384,524288,-6045696,28639232,-10190848,-503578624,2877128704,-11172184064,37191598080,-90904985600,133774098432,-94618451968,16498360320]),(⟨3,0,1⟩,[0,131072,-2785280,20971520,-68550656,111673344,-166658048,-1109655552,12864585728,-44822036480,67933405184,-39190265856]),(⟨3,0,2⟩,[32768,-851968,7864320,-28311552,8060928,204865536,-809893888,3057123328,-7621541888,7039025152,156893184]),(⟨3,0,3⟩,[0,-98304,1835008,-9568256,-786432,165609472,-823918592,3036545024,-7167279104,6810927104]),(⟨3,1,0⟩,[0,196608,-4489216,37552128,-143523840,278528000,-415956992,-651296768,13091602432,-48570892288,73031974912,-40009138176]),(⟨3,1,1⟩,[0,0,294912,-7077888,57016320,-128188416,-503119872,2687238144,-1858732032,-7220232192,9791373312]),(⟨3,1,2⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨3,1,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,2,0⟩,[32768,-851968,7864320,-28311552,8060928,204865536,-809893888,3057123328,-7621541888,7039025152,156893184]),(⟨3,2,1⟩,[32768,-589824,1441792,30932992,-235208704,484835328,444989440,-2370830336,1109950464,1473970176]),(⟨3,2,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,3,0⟩,[0,-98304,1835008,-9568256,-786432,165609472,-823918592,3036545024,-7167279104,6810927104]),(⟨3,3,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,0,0⟩,[16384,-327680,1589248,6619136,-80969728,230555648,-101285888,-1175322624,7999275008,-29328211968,50125684736,-31569936384]),(⟨4,0,1⟩,[16384,-425984,4243456,-21102592,58621952,-63111168,-348815360,1757806592,-1646968832,-4261052416,6802489344]),(⟨4,0,2⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨4,1,0⟩,[16384,-425984,3850240,-13762560,7766016,118292480,-789479424,2488664064,-1181925376,-8955527168,12214845440]),(⟨4,1,1⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨4,1,2⟩,[65536,-1572864,12320768,-21495808,-161087488,731381760,-428081152,-2125987840,2799763456]),(⟨4,2,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨4,2,1⟩,[65536,-1572864,12320768,-21495808,-161087488,731381760,-428081152,-2125987840,2799763456]),(⟨5,0,0⟩,[16384,-524288,5259264,-14680064,-61571072,505937920,-1737588736,5464129536,-12876300288,13410238464,-2144780288]),(⟨5,0,1⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨5,1,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨5,1,1⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨6,0,0⟩,[0,-98304,1835008,-9568256,-786432,165609472,-823918592,3036545024,-7167279104,6810927104])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial16)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 16))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound16 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨0,2,1⟩,[-128,1536,-3840,-4608,15232]),(⟨0,3,0⟩,[-128,1536,256,-37376,76672]),(⟨1,0,0⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨1,0,1⟩,[0,-512,6144,-15360,-18432,60928])]

noncomputable def partial8 : Poly := [(⟨0,2,1⟩,[-16384,458752,-5259264,32538624,-124289024,341835776,-796557312,1363083264,-133120000,-6224543744,13971406848,-11476893696,2246049792]),(⟨0,2,2⟩,[0,65536,-1441792,12615680,-60030976,193724416,-520617984,1016004608,-284950528,-4165533696,9175957504,-6305316864]),(⟨0,2,3⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨0,2,4⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨0,3,0⟩,[-16384,458752,-4734976,19955712,2588672,-384827392,2024112128,-7429226496,23655923712,-56622252032,83267076096,-59861336064,11305746432]),(⟨0,3,1⟩,[0,131072,-2883584,23134208,-82313216,99090432,284164096,-2643591168,13501988864,-40007499776,61234479104,-38043844608]),(⟨0,3,2⟩,[16384,-425984,3719168,-9568256,-33652736,267190272,-924483584,3000369152,-6684327936,5764382720,361611264]),(⟨0,3,3⟩,[0,-98304,1835008,-9568256,-786432,165609472,-823918592,3036545024,-7167279104,6810927104]),(⟨0,4,0⟩,[0,65536,-1441792,10518528,-22282240,-94633984,804782080,-3659595776,13786939392,-35841966080,52058521600,-31738527744]),(⟨0,4,1⟩,[16384,-425984,4243456,-21102592,58621952,-63111168,-348815360,1757806592,-1646968832,-4261052416,6802489344]),(⟨0,5,0⟩,[16384,-425984,3620864,-7208960,-53706752,330891264,-904626176,2507276288,-6109839360,6606651392,-1030471680]),(⟨0,5,1⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨0,6,0⟩,[0,-98304,1835008,-9568256,-786432,165609472,-823918592,3036545024,-7167279104,6810927104]),(⟨1,0,0⟩,[16384,-524288,6864896,-47153152,172949504,-209387520,-1196195840,8911257600,-37904433152,123979956224,-302901379072,508737912832,-531847151616,290040250368,-48884613120]),(⟨1,0,1⟩,[0,-131072,3538944,-38502400,220463104,-722927616,1314914304,-27328512,-12943360000,70313181184,-211630292992,373016788992,-358610370560,146217566208]),(⟨1,0,2⟩,[-32768,950272,-10616832,56131584,-124616704,-89849856,1375993856,-5605883904,17866719232,-38844727296,42563141632,-6183813120,-18519588864]),(⟨1,0,3⟩,[0,229376,-5373952,47874048,-205520896,426967040,-154402816,-2713387008,15605956608,-44788776960,64065241088,-36573773824]),(⟨1,0,4⟩,[16384,-425984,3751936,-11403264,-9142272,119078912,-326074368,787611648,-472170496,-3419832320,5207638016]),(⟨1,0,5⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨1,1,0⟩,[0,-131072,3538944,-38502400,220463104,-722927616,1314914304,-27328512,-12943360000,70313181184,-211630292992,373016788992,-358610370560,146217566208]),(⟨1,1,1⟩,[0,0,425984,-8781824,72810496,-369360896,1642790912,-6484918272,15703736320,-8836087808,-49610588160,116685406208,-80740810752]),(⟨1,1,2⟩,[0,131072,-3145728,29589504,-144441344,440795136,-1024720896,1394933760,1914437632,-10212343808,10905452544,-1555857408]),(⟨1,1,3⟩,[0,0,-294912,4980736,-30801920,117702656,-460521472,1223950336,-109445120,-5536743424,6804439040]),(⟨1,2,0⟩,[-32768,950272,-10616832,56131584,-124616704,-89849856,1375993856,-5605883904,17866719232,-38844727296,42563141632,-6183813120,-18519588864]),(⟨1,2,1⟩,[0,196608,-4587520,42205184,-204472320,634519552,-1545338880,2410938368,1629487104,-14377877504,20081410048,-7861174272]),(⟨1,2,2⟩,[32768,-851968,8388608,-39845888,103481344,-188350464,209321984,606601216,-2448916480,1707016192,982646784]),(⟨1,2,3⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨1,3,0⟩,[0,294912,-6815744,58392576,-227803136,332333056,650379264,-6372982784,29392896000,-80630743040,116123762688,-68312301568]),(⟨1,3,1⟩,[0,0,-98304,262144,6160384,53215232,-943783936,3418095616,-1393688576,-11914706944,15203729408]),(⟨1,3,2⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨1,3,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,4,0⟩,[16384,-425984,3850240,-13762560,7766016,118292480,-789479424,2488664064,-1181925376,-8955527168,12214845440]),(⟨1,4,2⟩,[65536,-1572864,12320768,-21495808,-161087488,731381760,-428081152,-2125987840,2799763456]),(⟨1,5,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨1,5,1⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨2,0,0⟩,[-16384,360448,-2375680,-2523136,111312896,-646316032,2026733568,-4333043712,4823891968,16359456768,-105686581248,253446291456,-293562023936,135383678976]),(⟨2,0,1⟩,[-16384,524288,-6406144,38207488,-114720768,93847552,924352512,-6782320640,25042272256,-48203563008,31529975808,33747566592,-48080879616]),(⟨2,0,2⟩,[16384,-262144,147456,21725184,-188186624,792854528,-2202107904,4436852736,-4385193984,-4115267584,13050003456,-6873710592]),(⟨2,0,3⟩,[16384,-524288,5881856,-28573696,53903360,49020928,-738230272,3506700288,-8278163456,7235960832,73056256]),(⟨2,0,4⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨2,1,0⟩,[-16384,524288,-6406144,38207488,-114720768,93847552,924352512,-6782320640,25042272256,-48203563008,31529975808,33747566592,-48080879616]),(⟨2,1,1⟩,[0,131072,-2785280,23855104,-125173760,560463872,-2001666048,3407085568,2737438720,-17741512704,18312691712,-2620391424]),(⟨2,1,2⟩,[-16384,491520,-5029888,13500416,112820224,-963051520,2600108032,-1142554624,-7514963968,14016020480,-7519977472]),(⟨2,1,3⟩,[0,32768,-1310720,14024704,-39583744,-136642560,840171520,-649723904,-2296643584,3209199616]),(⟨2,1,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,2,0⟩,[16384,-262144,147456,21725184,-188186624,792854528,-2202107904,4436852736,-4385193984,-4115267584,13050003456,-6873710592]),(⟨2,2,1⟩,[0,65536,-884736,-5242880,154533888,-1025376256,2714697728,-1085800448,-8452177920,15290662912,-7724695552]),(⟨2,2,2⟩,[0,262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨2,2,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,3,0⟩,[32768,-950272,9502720,-35782656,196608,379912192,-1642856448,6013976576,-14388002816,13842612224,-957415424]),(⟨2,3,1⟩,[0,32768,-1310720,14024704,-39583744,-136642560,840171520,-649723904,-2296643584,3209199616]),(⟨2,3,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,4,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨2,4,1⟩,[65536,-1572864,12320768,-21495808,-161087488,731381760,-428081152,-2125987840,2799763456]),(⟨3,0,0⟩,[-32768,1015808,-11665408,57999360,-60981248,-695140352,4274782208,-16058679296,51127418880,-122385367040,179027968000,-126029201408,20953989120]),(⟨3,0,1⟩,[0,196608,-4489216,37552128,-143523840,278528000,-415956992,-651296768,13091602432,-48570892288,73031974912,-40009138176]),(⟨3,0,2⟩,[32768,-851968,7864320,-28311552,8060928,204865536,-809893888,3057123328,-7621541888,7039025152,156893184]),(⟨3,0,3⟩,[0,-98304,1835008,-9568256,-786432,165609472,-823918592,3036545024,-7167279104,6810927104]),(⟨3,1,0⟩,[0,196608,-4489216,37552128,-143523840,278528000,-415956992,-651296768,13091602432,-48570892288,73031974912,-40009138176]),(⟨3,1,1⟩,[-32768,917504,-9076736,29884416,88014848,-901513216,2022113280,501743616,-7287504896,7205683200,-308051968]),(⟨3,1,2⟩,[32768,-589824,1441792,30932992,-235208704,484835328,444989440,-2370830336,1109950464,1473970176]),(⟨3,1,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,2,0⟩,[32768,-851968,7864320,-28311552,8060928,204865536,-809893888,3057123328,-7621541888,7039025152,156893184]),(⟨3,2,1⟩,[32768,-688128,3276800,18219008,-189857792,374669312,627703808,-2254569472,-63668224,2827059200]),(⟨3,2,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,3,0⟩,[0,-196608,3670016,-19136512,-1572864,331218944,-1647837184,6073090048,-14334558208,13621854208]),(⟨3,3,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,0,0⟩,[16384,-229376,-638976,25296896,-151486464,296943616,514228224,-5363073024,23663165440,-66202599424,99916398592,-61019521024]),(⟨4,0,1⟩,[16384,-425984,3850240,-13762560,7766016,118292480,-789479424,2488664064,-1181925376,-8955527168,12214845440]),(⟨4,0,2⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨4,1,0⟩,[16384,-425984,3850240,-13762560,7766016,118292480,-789479424,2488664064,-1181925376,-8955527168,12214845440]),(⟨4,1,1⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨4,1,2⟩,[65536,-1572864,12320768,-21495808,-161087488,731381760,-428081152,-2125987840,2799763456]),(⟨4,2,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨4,2,1⟩,[65536,-1572864,12320768,-21495808,-161087488,731381760,-428081152,-2125987840,2799763456]),(⟨5,0,0⟩,[16384,-524288,5259264,-14680064,-61571072,505937920,-1737588736,5464129536,-12876300288,13410238464,-2144780288]),(⟨5,0,1⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨5,1,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨5,1,1⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨6,0,0⟩,[0,-98304,1835008,-9568256,-786432,165609472,-823918592,3036545024,-7167279104,6810927104])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,1,0⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨0,1,1⟩,[0,-512,6144,-15360,-18432,60928]),(⟨0,1,2⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[-128,1280,1280,-34816,69504,-12544])]

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[16384,-524288,6864896,-47153152,172949504,-209387520,-1196195840,8911257600,-37904433152,123979956224,-302901379072,508737912832,-531847151616,290040250368,-48884613120]),(⟨0,1,1⟩,[0,-131072,3538944,-38502400,220463104,-722927616,1314914304,-27328512,-12943360000,70313181184,-211630292992,373016788992,-358610370560,146217566208]),(⟨0,1,2⟩,[-32768,950272,-10616832,56131584,-124616704,-89849856,1375993856,-5605883904,17866719232,-38844727296,42563141632,-6183813120,-18519588864]),(⟨0,1,3⟩,[0,229376,-5373952,47874048,-205520896,426967040,-154402816,-2713387008,15605956608,-44788776960,64065241088,-36573773824]),(⟨0,1,4⟩,[16384,-425984,3751936,-11403264,-9142272,119078912,-326074368,787611648,-472170496,-3419832320,5207638016]),(⟨0,1,5⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨0,2,0⟩,[-16384,360448,-2375680,-2523136,111312896,-646316032,2026733568,-4333043712,4823891968,16359456768,-105686581248,253446291456,-293562023936,135383678976]),(⟨0,2,1⟩,[-16384,524288,-6406144,38207488,-114720768,93847552,924352512,-6782320640,25042272256,-48203563008,31529975808,33747566592,-48080879616]),(⟨0,2,2⟩,[16384,-262144,147456,21725184,-188186624,792854528,-2202107904,4436852736,-4385193984,-4115267584,13050003456,-6873710592]),(⟨0,2,3⟩,[16384,-524288,5881856,-28573696,53903360,49020928,-738230272,3506700288,-8278163456,7235960832,73056256]),(⟨0,2,4⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨0,3,0⟩,[-32768,1015808,-11665408,57999360,-60981248,-695140352,4274782208,-16058679296,51127418880,-122385367040,179027968000,-126029201408,20953989120]),(⟨0,3,1⟩,[0,196608,-4489216,37552128,-143523840,278528000,-415956992,-651296768,13091602432,-48570892288,73031974912,-40009138176]),(⟨0,3,2⟩,[32768,-851968,7864320,-28311552,8060928,204865536,-809893888,3057123328,-7621541888,7039025152,156893184]),(⟨0,3,3⟩,[0,-98304,1835008,-9568256,-786432,165609472,-823918592,3036545024,-7167279104,6810927104]),(⟨0,4,0⟩,[16384,-229376,-638976,25296896,-151486464,296943616,514228224,-5363073024,23663165440,-66202599424,99916398592,-61019521024]),(⟨0,4,1⟩,[16384,-425984,3850240,-13762560,7766016,118292480,-789479424,2488664064,-1181925376,-8955527168,12214845440]),(⟨0,4,2⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨0,5,0⟩,[16384,-524288,5259264,-14680064,-61571072,505937920,-1737588736,5464129536,-12876300288,13410238464,-2144780288]),(⟨0,5,1⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨0,6,0⟩,[0,-98304,1835008,-9568256,-786432,165609472,-823918592,3036545024,-7167279104,6810927104]),(⟨1,0,0⟩,[16384,-524288,6864896,-47153152,172949504,-209387520,-1196195840,8911257600,-37904433152,123979956224,-302901379072,508737912832,-531847151616,290040250368,-48884613120]),(⟨1,0,1⟩,[0,-131072,3538944,-38502400,220463104,-722927616,1314914304,-27328512,-12943360000,70313181184,-211630292992,373016788992,-358610370560,146217566208]),(⟨1,0,2⟩,[-32768,950272,-10616832,56131584,-124616704,-89849856,1375993856,-5605883904,17866719232,-38844727296,42563141632,-6183813120,-18519588864]),(⟨1,0,3⟩,[0,229376,-5373952,47874048,-205520896,426967040,-154402816,-2713387008,15605956608,-44788776960,64065241088,-36573773824]),(⟨1,0,4⟩,[16384,-425984,3751936,-11403264,-9142272,119078912,-326074368,787611648,-472170496,-3419832320,5207638016]),(⟨1,0,5⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨1,1,0⟩,[0,-196608,5242880,-55967744,310771712,-948699136,1262485504,3131572224,-31339053056,141158842368,-398362411008,690147950592,-671313166336,283450933248]),(⟨1,1,1⟩,[0,0,589824,-11796480,95158272,-498597888,2510684160,-10887364608,27343454208,-16532373504,-82559041536,196666982400,-136260354048]),(⟨1,1,2⟩,[0,196608,-4587520,42598400,-213909504,714735616,-1800142848,2331508736,3601858560,-16675831808,16712335360,-2292842496]),(⟨1,1,3⟩,[0,0,-196608,2621440,-10747904,54001664,-480378880,1717043200,-683933696,-6379012096,8196521984]),(⟨1,2,0⟩,[-32768,1015808,-12025856,67567616,-165511168,-97714176,2322006016,-11668815872,38978093056,-79683944448,76783845376,2336817152,-43625250816]),(⟨1,2,1⟩,[0,196608,-4489216,40435712,-200146944,727318528,-2250964992,3865444352,2964455424,-21490368512,23411261440,-3439263744]),(⟨1,2,2⟩,[0,65536,-884736,-5242880,154533888,-1025376256,2714697728,-1085800448,-8452177920,15290662912,-7724695552]),(⟨1,2,3⟩,[0,32768,-1310720,14024704,-39583744,-136642560,840171520,-649723904,-2296643584,3209199616]),(⟨1,2,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,3,0⟩,[0,294912,-6717440,56229888,-214040576,344915968,199557120,-4839047168,28755492864,-85445279744,122822688768,-69458722816]),(⟨1,3,1⟩,[-32768,917504,-9469952,37224448,37158912,-720109568,1581449216,1232601088,-6822461440,2511208448,5104304128]),(⟨1,3,2⟩,[32768,-688128,3276800,18219008,-189857792,374669312,627703808,-2254569472,-63668224,2827059200]),(⟨1,3,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,4,0⟩,[16384,-425984,3850240,-13762560,7766016,118292480,-789479424,2488664064,-1181925376,-8955527168,12214845440]),(⟨1,4,1⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨1,4,2⟩,[65536,-1572864,12320768,-21495808,-161087488,731381760,-428081152,-2125987840,2799763456]),(⟨1,5,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨1,5,1⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨2,0,0⟩,[-16384,360448,-2375680,-2523136,111312896,-646316032,2026733568,-4333043712,4823891968,16359456768,-105686581248,253446291456,-293562023936,135383678976]),(⟨2,0,1⟩,[-16384,524288,-6406144,38207488,-114720768,93847552,924352512,-6782320640,25042272256,-48203563008,31529975808,33747566592,-48080879616]),(⟨2,0,2⟩,[16384,-262144,147456,21725184,-188186624,792854528,-2202107904,4436852736,-4385193984,-4115267584,13050003456,-6873710592]),(⟨2,0,3⟩,[16384,-524288,5881856,-28573696,53903360,49020928,-738230272,3506700288,-8278163456,7235960832,73056256]),(⟨2,0,4⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨2,1,0⟩,[-32768,1015808,-12025856,67567616,-165511168,-97714176,2322006016,-11668815872,38978093056,-79683944448,76783845376,2336817152,-43625250816]),(⟨2,1,1⟩,[0,196608,-4489216,40435712,-200146944,727318528,-2250964992,3865444352,2964455424,-21490368512,23411261440,-3439263744]),(⟨2,1,2⟩,[0,65536,-884736,-5242880,154533888,-1025376256,2714697728,-1085800448,-8452177920,15290662912,-7724695552]),(⟨2,1,3⟩,[0,32768,-1310720,14024704,-39583744,-136642560,840171520,-649723904,-2296643584,3209199616]),(⟨2,1,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,2,0⟩,[32768,-655360,3178496,17825792,-246874112,1118044160,-3108175872,6921125888,-10172858368,2398486528,11117166592,-6705119232]),(⟨2,2,1⟩,[-32768,983040,-10256384,31719424,185532416,-1798701056,5239930880,-3271294976,-13880950784,29716578304,-17824120832]),(⟨2,2,2⟩,[0,393216,-9437184,80216064,-254803968,-79429632,1972371456,-2297954304,-3369074688,5568331776]),(⟨2,2,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,3,0⟩,[32768,-950272,9502720,-35782656,196608,379912192,-1642856448,6013976576,-14388002816,13842612224,-957415424]),(⟨2,3,1⟩,[32768,-688128,3276800,18219008,-189857792,374669312,627703808,-2254569472,-63668224,2827059200]),(⟨2,3,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,4,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨2,4,1⟩,[65536,-1572864,12320768,-21495808,-161087488,731381760,-428081152,-2125987840,2799763456]),(⟨3,0,0⟩,[-32768,1015808,-11665408,57999360,-60981248,-695140352,4274782208,-16058679296,51127418880,-122385367040,179027968000,-126029201408,20953989120]),(⟨3,0,1⟩,[0,196608,-4489216,37552128,-143523840,278528000,-415956992,-651296768,13091602432,-48570892288,73031974912,-40009138176]),(⟨3,0,2⟩,[32768,-851968,7864320,-28311552,8060928,204865536,-809893888,3057123328,-7621541888,7039025152,156893184]),(⟨3,0,3⟩,[0,-98304,1835008,-9568256,-786432,165609472,-823918592,3036545024,-7167279104,6810927104]),(⟨3,1,0⟩,[0,294912,-6717440,56229888,-214040576,344915968,199557120,-4839047168,28755492864,-85445279744,122822688768,-69458722816]),(⟨3,1,1⟩,[-32768,917504,-9469952,37224448,37158912,-720109568,1581449216,1232601088,-6822461440,2511208448,5104304128]),(⟨3,1,2⟩,[32768,-688128,3276800,18219008,-189857792,374669312,627703808,-2254569472,-63668224,2827059200]),(⟨3,1,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,2,0⟩,[32768,-950272,9502720,-35782656,196608,379912192,-1642856448,6013976576,-14388002816,13842612224,-957415424]),(⟨3,2,1⟩,[32768,-688128,3276800,18219008,-189857792,374669312,627703808,-2254569472,-63668224,2827059200]),(⟨3,2,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,3,0⟩,[0,-196608,3670016,-19136512,-1572864,331218944,-1647837184,6073090048,-14334558208,13621854208]),(⟨3,3,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,0,0⟩,[16384,-229376,-638976,25296896,-151486464,296943616,514228224,-5363073024,23663165440,-66202599424,99916398592,-61019521024]),(⟨4,0,1⟩,[16384,-425984,3850240,-13762560,7766016,118292480,-789479424,2488664064,-1181925376,-8955527168,12214845440]),(⟨4,0,2⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨4,1,0⟩,[16384,-425984,3850240,-13762560,7766016,118292480,-789479424,2488664064,-1181925376,-8955527168,12214845440]),(⟨4,1,1⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨4,1,2⟩,[65536,-1572864,12320768,-21495808,-161087488,731381760,-428081152,-2125987840,2799763456]),(⟨4,2,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨4,2,1⟩,[65536,-1572864,12320768,-21495808,-161087488,731381760,-428081152,-2125987840,2799763456]),(⟨5,0,0⟩,[16384,-524288,5259264,-14680064,-61571072,505937920,-1737588736,5464129536,-12876300288,13410238464,-2144780288]),(⟨5,0,1⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨5,1,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨5,1,1⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨6,0,0⟩,[0,-98304,1835008,-9568256,-786432,165609472,-823918592,3036545024,-7167279104,6810927104])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,0⟩,[128,-1792,5120,30720,-231808,574208,-567040,116736]),(⟨0,0,1⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨0,0,2⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨0,0,3⟩,[-128,1536,256,-37376,76672])]

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[16384,-491520,5947392,-35061760,70909952,413270016,-4108615680,19782172672,-71529512960,211848953856,-492257034240,824179097600,-904977481728,573005561856,-166363398144,17213423616]),(⟨0,0,1⟩,[16384,-589824,8437760,-61734912,231735296,-204996608,-2493808640,17315659776,-74202857472,245323988992,-604060794880,1019573305344,-1067378704384,580472143872,-97207713792]),(⟨0,0,2⟩,[-32768,819200,-7143424,16973824,131825664,-1202585600,4799987712,-13196328960,28217081856,-34035040256,-32207339520,195816914944,-276646952960,133814747136]),(⟨0,0,3⟩,[-32768,1114112,-13697024,73007104,-96632832,-853147648,5942673408,-23962583040,77006274560,-180805894144,260221108224,-182257844224,31323881472]),(⟨0,0,4⟩,[16384,-229376,-638976,25296896,-151486464,296943616,514228224,-5363073024,23663165440,-66202599424,99916398592,-61019521024]),(⟨0,0,5⟩,[16384,-524288,5259264,-14680064,-61571072,505937920,-1737588736,5464129536,-12876300288,13410238464,-2144780288]),(⟨0,0,6⟩,[0,-98304,1835008,-9568256,-786432,165609472,-823918592,3036545024,-7167279104,6810927104]),(⟨0,1,0⟩,[16384,-589824,8437760,-61734912,231735296,-204996608,-2493808640,17315659776,-74202857472,245323988992,-604060794880,1019573305344,-1067378704384,580472143872,-97207713792]),(⟨0,1,1⟩,[0,-196608,5144576,-53411840,287375360,-887357440,1666908160,-458883072,-20652228608,131830185984,-421283069952,755613892608,-726363602944,294119669760]),(⟨0,1,2⟩,[-32768,1015808,-12025856,67567616,-165511168,-97714176,2322006016,-11668815872,38978093056,-79683944448,76783845376,2336817152,-43625250816]),(⟨0,1,3⟩,[0,294912,-6717440,56229888,-214040576,344915968,199557120,-4839047168,28755492864,-85445279744,122822688768,-69458722816]),(⟨0,1,4⟩,[16384,-425984,3850240,-13762560,7766016,118292480,-789479424,2488664064,-1181925376,-8955527168,12214845440]),(⟨0,1,5⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨0,2,0⟩,[-32768,819200,-7143424,16973824,131825664,-1202585600,4799987712,-13196328960,28217081856,-34035040256,-32207339520,195816914944,-276646952960,133814747136]),(⟨0,2,1⟩,[-32768,1015808,-12025856,67567616,-165511168,-97714176,2322006016,-11668815872,38978093056,-79683944448,76783845376,2336817152,-43625250816]),(⟨0,2,2⟩,[32768,-655360,3178496,17825792,-246874112,1118044160,-3108175872,6921125888,-10172858368,2398486528,11117166592,-6705119232]),(⟨0,2,3⟩,[32768,-950272,9502720,-35782656,196608,379912192,-1642856448,6013976576,-14388002816,13842612224,-957415424]),(⟨0,2,4⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨0,3,0⟩,[-32768,1114112,-13697024,73007104,-96632832,-853147648,5942673408,-23962583040,77006274560,-180805894144,260221108224,-182257844224,31323881472]),(⟨0,3,1⟩,[0,294912,-6717440,56229888,-214040576,344915968,199557120,-4839047168,28755492864,-85445279744,122822688768,-69458722816]),(⟨0,3,2⟩,[32768,-950272,9502720,-35782656,196608,379912192,-1642856448,6013976576,-14388002816,13842612224,-957415424]),(⟨0,3,3⟩,[0,-196608,3670016,-19136512,-1572864,331218944,-1647837184,6073090048,-14334558208,13621854208]),(⟨0,4,0⟩,[16384,-229376,-638976,25296896,-151486464,296943616,514228224,-5363073024,23663165440,-66202599424,99916398592,-61019521024]),(⟨0,4,1⟩,[16384,-425984,3850240,-13762560,7766016,118292480,-789479424,2488664064,-1181925376,-8955527168,12214845440]),(⟨0,4,2⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨0,5,0⟩,[16384,-524288,5259264,-14680064,-61571072,505937920,-1737588736,5464129536,-12876300288,13410238464,-2144780288]),(⟨0,5,1⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨0,6,0⟩,[0,-98304,1835008,-9568256,-786432,165609472,-823918592,3036545024,-7167279104,6810927104]),(⟨1,0,0⟩,[16384,-589824,8437760,-61734912,231735296,-204996608,-2493808640,17315659776,-74202857472,245323988992,-604060794880,1019573305344,-1067378704384,580472143872,-97207713792]),(⟨1,0,1⟩,[0,-196608,5144576,-53411840,287375360,-887357440,1666908160,-458883072,-20652228608,131830185984,-421283069952,755613892608,-726363602944,294119669760]),(⟨1,0,2⟩,[-32768,1015808,-12025856,67567616,-165511168,-97714176,2322006016,-11668815872,38978093056,-79683944448,76783845376,2336817152,-43625250816]),(⟨1,0,3⟩,[0,294912,-6717440,56229888,-214040576,344915968,199557120,-4839047168,28755492864,-85445279744,122822688768,-69458722816]),(⟨1,0,4⟩,[16384,-425984,3850240,-13762560,7766016,118292480,-789479424,2488664064,-1181925376,-8955527168,12214845440]),(⟨1,0,5⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨1,1,0⟩,[0,-196608,5144576,-53411840,287375360,-887357440,1666908160,-458883072,-20652228608,131830185984,-421283069952,755613892608,-726363602944,294119669760]),(⟨1,1,1⟩,[0,0,491520,-9043968,67043328,-387710976,2603679744,-13207339008,34919153664,-23088857088,-98845360128,239944728576,-166558629888]),(⟨1,1,2⟩,[-32768,1048576,-12288000,60882944,-65339392,-469499904,1311309824,755892224,-4675764224,331612160,5061115904,116981760]),(⟨1,1,3⟩,[-32768,917504,-9469952,37224448,37158912,-720109568,1581449216,1232601088,-6822461440,2511208448,5104304128]),(⟨1,1,4⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨1,1,5⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨1,2,0⟩,[-32768,1015808,-12025856,67567616,-165511168,-97714176,2322006016,-11668815872,38978093056,-79683944448,76783845376,2336817152,-43625250816]),(⟨1,2,1⟩,[-32768,1048576,-12288000,60882944,-65339392,-469499904,1311309824,755892224,-4675764224,331612160,5061115904,116981760]),(⟨1,2,2⟩,[-32768,983040,-10256384,31719424,185532416,-1798701056,5239930880,-3271294976,-13880950784,29716578304,-17824120832]),(⟨1,2,3⟩,[32768,-688128,3276800,18219008,-189857792,374669312,627703808,-2254569472,-63668224,2827059200]),(⟨1,2,4⟩,[65536,-1572864,12320768,-21495808,-161087488,731381760,-428081152,-2125987840,2799763456]),(⟨1,3,0⟩,[0,294912,-6717440,56229888,-214040576,344915968,199557120,-4839047168,28755492864,-85445279744,122822688768,-69458722816]),(⟨1,3,1⟩,[-32768,917504,-9469952,37224448,37158912,-720109568,1581449216,1232601088,-6822461440,2511208448,5104304128]),(⟨1,3,2⟩,[32768,-688128,3276800,18219008,-189857792,374669312,627703808,-2254569472,-63668224,2827059200]),(⟨1,3,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,4,0⟩,[16384,-425984,3850240,-13762560,7766016,118292480,-789479424,2488664064,-1181925376,-8955527168,12214845440]),(⟨1,4,1⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨1,4,2⟩,[65536,-1572864,12320768,-21495808,-161087488,731381760,-428081152,-2125987840,2799763456]),(⟨1,5,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨1,5,1⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨2,0,0⟩,[-32768,819200,-7143424,16973824,131825664,-1202585600,4799987712,-13196328960,28217081856,-34035040256,-32207339520,195816914944,-276646952960,133814747136]),(⟨2,0,1⟩,[-32768,1015808,-12025856,67567616,-165511168,-97714176,2322006016,-11668815872,38978093056,-79683944448,76783845376,2336817152,-43625250816]),(⟨2,0,2⟩,[32768,-655360,3178496,17825792,-246874112,1118044160,-3108175872,6921125888,-10172858368,2398486528,11117166592,-6705119232]),(⟨2,0,3⟩,[32768,-950272,9502720,-35782656,196608,379912192,-1642856448,6013976576,-14388002816,13842612224,-957415424]),(⟨2,0,4⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨2,1,0⟩,[-32768,1015808,-12025856,67567616,-165511168,-97714176,2322006016,-11668815872,38978093056,-79683944448,76783845376,2336817152,-43625250816]),(⟨2,1,1⟩,[-32768,1048576,-12288000,60882944,-65339392,-469499904,1311309824,755892224,-4675764224,331612160,5061115904,116981760]),(⟨2,1,2⟩,[-32768,983040,-10256384,31719424,185532416,-1798701056,5239930880,-3271294976,-13880950784,29716578304,-17824120832]),(⟨2,1,3⟩,[32768,-688128,3276800,18219008,-189857792,374669312,627703808,-2254569472,-63668224,2827059200]),(⟨2,1,4⟩,[65536,-1572864,12320768,-21495808,-161087488,731381760,-428081152,-2125987840,2799763456]),(⟨2,2,0⟩,[32768,-655360,3178496,17825792,-246874112,1118044160,-3108175872,6921125888,-10172858368,2398486528,11117166592,-6705119232]),(⟨2,2,1⟩,[-32768,983040,-10256384,31719424,185532416,-1798701056,5239930880,-3271294976,-13880950784,29716578304,-17824120832]),(⟨2,2,2⟩,[0,393216,-9437184,80216064,-254803968,-79429632,1972371456,-2297954304,-3369074688,5568331776]),(⟨2,2,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,3,0⟩,[32768,-950272,9502720,-35782656,196608,379912192,-1642856448,6013976576,-14388002816,13842612224,-957415424]),(⟨2,3,1⟩,[32768,-688128,3276800,18219008,-189857792,374669312,627703808,-2254569472,-63668224,2827059200]),(⟨2,3,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,4,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨2,4,1⟩,[65536,-1572864,12320768,-21495808,-161087488,731381760,-428081152,-2125987840,2799763456]),(⟨3,0,0⟩,[-32768,1114112,-13697024,73007104,-96632832,-853147648,5942673408,-23962583040,77006274560,-180805894144,260221108224,-182257844224,31323881472]),(⟨3,0,1⟩,[0,294912,-6717440,56229888,-214040576,344915968,199557120,-4839047168,28755492864,-85445279744,122822688768,-69458722816]),(⟨3,0,2⟩,[32768,-950272,9502720,-35782656,196608,379912192,-1642856448,6013976576,-14388002816,13842612224,-957415424]),(⟨3,0,3⟩,[0,-196608,3670016,-19136512,-1572864,331218944,-1647837184,6073090048,-14334558208,13621854208]),(⟨3,1,0⟩,[0,294912,-6717440,56229888,-214040576,344915968,199557120,-4839047168,28755492864,-85445279744,122822688768,-69458722816]),(⟨3,1,1⟩,[-32768,917504,-9469952,37224448,37158912,-720109568,1581449216,1232601088,-6822461440,2511208448,5104304128]),(⟨3,1,2⟩,[32768,-688128,3276800,18219008,-189857792,374669312,627703808,-2254569472,-63668224,2827059200]),(⟨3,1,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,2,0⟩,[32768,-950272,9502720,-35782656,196608,379912192,-1642856448,6013976576,-14388002816,13842612224,-957415424]),(⟨3,2,1⟩,[32768,-688128,3276800,18219008,-189857792,374669312,627703808,-2254569472,-63668224,2827059200]),(⟨3,2,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,3,0⟩,[0,-196608,3670016,-19136512,-1572864,331218944,-1647837184,6073090048,-14334558208,13621854208]),(⟨3,3,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,0,0⟩,[16384,-229376,-638976,25296896,-151486464,296943616,514228224,-5363073024,23663165440,-66202599424,99916398592,-61019521024]),(⟨4,0,1⟩,[16384,-425984,3850240,-13762560,7766016,118292480,-789479424,2488664064,-1181925376,-8955527168,12214845440]),(⟨4,0,2⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨4,1,0⟩,[16384,-425984,3850240,-13762560,7766016,118292480,-789479424,2488664064,-1181925376,-8955527168,12214845440]),(⟨4,1,1⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨4,1,2⟩,[65536,-1572864,12320768,-21495808,-161087488,731381760,-428081152,-2125987840,2799763456]),(⟨4,2,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨4,2,1⟩,[65536,-1572864,12320768,-21495808,-161087488,731381760,-428081152,-2125987840,2799763456]),(⟨5,0,0⟩,[16384,-524288,5259264,-14680064,-61571072,505937920,-1737588736,5464129536,-12876300288,13410238464,-2144780288]),(⟨5,0,1⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨5,1,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨5,1,1⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨6,0,0⟩,[0,-98304,1835008,-9568256,-786432,165609472,-823918592,3036545024,-7167279104,6810927104])]


theorem partial_checked0 :
    (Poly.add (Poly.add (Poly.mul chunk0 sourceRight) partial4)
      (Poly.scale (K.ofRat (-1)) partial0)).isZero := by decide +kernel

theorem partial_sound0 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 0)
      sourceRight).eval u v t=partial0.eval u v t := by
  change (Poly.mul (chunk0++(sourceLeft.drop 4))
    sourceRight).eval u v t=partial0.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound4 partial_checked0 u v t


theorem weighted_checked :
    (Poly.add (Poly.scale (K.ofRat r499) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 3 11).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r498*r498 : ℚ)=r499 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 3 11 r498 r498 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 3=11 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 3 11).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C092

#print axioms Coulomb8.Columns.C092.sound
