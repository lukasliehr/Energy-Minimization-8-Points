import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C139

def r0 : ℚ := { num := 262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -11173888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 31031296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -2565079040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 20641939456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -120057528320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 520698134528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -1707906105344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 4243701956608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -7933402841088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 11130894942208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -43000004608, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 14161134551040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -20465359224832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 27520965869568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -23515182333952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 7960550113280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 3014642827264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -2665182953472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 59691368448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := 131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -1081344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := 25853952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := -2469396480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := 3133931520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -135897612288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := 87071522816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := -2015118491648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 4929137147904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -8871956185088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 1688577703936, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -12966872219648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 16373532852224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -25844526284800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 33109116059648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -24085857042432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 4282194984960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 706053701632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -35775479808, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -524288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 20119552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -337281024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 3269099520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -20355645440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 84839333888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -1972338688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 390917423104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -209263034368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -624040640512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 1563488714752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -91128365056, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 1541024022528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -4319219253248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 1165209993216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -6498044641280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 65089142784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 28728066048, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 13139968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -313819136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 3980689408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := -31254020096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := 163680911360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -592601710592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 213766078464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := -2599696498688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := 3054211268608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := -2783661096960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := 3724321849344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -6716756557824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 7530944495616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -2994137038848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -1123397042176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 74651172864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -8290304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 13631488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -382664704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := -1690173440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := 3908534272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := -21282029568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := 464196075520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := -893280321536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := 151894196224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := -54675636224, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 1407676121088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -166599720960, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := 3112976220160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := -144044589056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -10020716544, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := -5701632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 136642560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -1577844736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 10484514816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -6167527424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := 112094412800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -3603955712, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := 151560323072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -87430070272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 205274415104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -59965702144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 254281711616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 15752298496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -912064512, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 3538944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -410779648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 3475898368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := -17211064320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 180617216, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -13569097728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 94830854144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -60442017792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 129794965504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -283791589376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 201516777472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 5018222592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 1179648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -20709376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 14712832, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -137953280, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 17232723968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -96744177664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 406237773824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -1256553578496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 2814434508800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -4478019239936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 5198038007808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := -5975868637184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 10709690187776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -19218669830144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 3021771276288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -9487020818432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -453916852224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := 75058053120, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 196608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -82313216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 188940288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := -11334778880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := 1241055232, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := -31166300160, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := 538936934400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -19044564992, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := 10006102016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := -77972111360, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := 1539756720128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := -206802714624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 76971048960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -597688320, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 22618767360, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -29492248576, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -65536, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 360448, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := -193069056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 1692434432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -11667570688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := 59355004928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := -30563237888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := 531216564224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := -878982660096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 961622081536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -963362291712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 255374557184, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -3256865193984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 3055176679424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -101450383360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -10752884736, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := -262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 983040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := -77660160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := 507117568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -2139488256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 5919932416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -9083486208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -3351511040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 3341287424, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := -132112252928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := 86667493376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 193244823552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -377325748224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := 39518208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 381878272, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := 524288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := -19464192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 306577408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := -2695364608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := 2092171264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -51205308416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := 114743705600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := -154599817216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := 105519251456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := -7293435904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 189878894592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -410054819840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 36998217728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := 4670029824, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := -9849405440, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := 7251034112, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := -4194304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := 56360960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -390987776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 72744960, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := 1225129984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := -27196391424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := 15911878656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -228502667264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 231371177984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := -111895904256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := 264416919552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -708588208128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := 11537350656, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := 795869184, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := -786432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := 20578304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -31326208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 173932544, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := -3584425984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 4029939712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := 6245056512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -23237230592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 14585167872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := 17550147584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := 14660534272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := -15691546624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := 114950144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := -131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := 3932160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := -393216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := 279183360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -119013376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 746061824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := 137101312, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -6217531392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := 1412300800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := 831782912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 6685589504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -2094268416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -2359296, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 1048576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -23330816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := 198443008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := -112197632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := 1143996416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := 1527250944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -6331826176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := 1894776832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 429916160, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := 8593866752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := -185860096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := -2097152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := 50331648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := -25165824, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := 1358954496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 423624704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -10519314432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := 12255756288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := 150994944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := 589824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -17793024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 236814336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -1865318400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := 9755983872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := -5048008704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := 85677539328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -105984589824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -114358714368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := 119197040640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := -1660287418368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := 917555675136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := 2417201086464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := -692651261952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := 22061678592, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 110965456896, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := -5842894848, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 16220160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := -135200768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := 728203264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := -382402560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := 6642696192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := -9109700608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := -4945051648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 57047580672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -128268468224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := 123191099392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := 12044369920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := -2837381120, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := 4500914176, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -11941773312, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 825294848, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -36306944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 534380544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -626262016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 21982216192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -68159930368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := 116123762688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := -21567635456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -55187341312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := 53985542144, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := -947816103936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := 312674091008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := 25397166080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -119144448, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := -19791872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := 312082432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -9306112, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 1973288960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -42253156352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 65629585408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := 11011358720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := -37903663104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := 74780639232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := -8876064768, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := 1037697024, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 134873088, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -1048576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 32636928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := -407896064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := 372375552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := -8820621312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := 1875640320, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := 7461666816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := -216268800, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := 13810794496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -906362880, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := -535822336, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := 19267584, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 262144, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := -220725248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 1825570816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -7891058688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 16428564480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -3651141632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := -56521392128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := 6580600832, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := -9299034112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -14155776, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 7602176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := -88473600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := 531365888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := -246022144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := 2414346240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := 2514747392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := -16572219392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 28557967360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -2885943296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := -20635844608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := 13191348224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := -111542272, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := -12582912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := 6291456, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := -339738624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := -105906176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := 2629828608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := -3063939072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := -37748736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := 3145728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -69992448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 595329024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := -336592896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := 3431989248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := 4581752832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := -18995478528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := 5684330496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := 1289748480, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := 25781600256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -557580288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := -5586944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := 15515648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := -1282539520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := 10320969728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := -60028764160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := 260349067264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := -853953052672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := 2121850978304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -3966701420544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := 5565447471104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := -21500002304, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := 7080567275520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := -10232679612416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := 13760482934784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := -11757591166976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := 3980275056640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := 1507321413632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := -1332591476736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := 29845684224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := -540672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := 12926976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := -1234698240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := 1566965760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := -67948806144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := 43535761408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := -1007559245824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 2464568573952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := -4435978092544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := 844288851968, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := -6483436109824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := 8186766426112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := -12922263142400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := 16554558029824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := -12042928521216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := 2141097492480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := 353026850816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := -17887739904, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := 10059776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := -168640512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := 1634549760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := -10177822720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := 42419666944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := -986169344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := 195458711552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := -104631517184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := -312020320256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := 781744357376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := -45564182528, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := 770512011264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := -2159609626624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := 582604996608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := -3249022320640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := 32544571392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := 14364033024, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := -98304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := 6569984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := -156909568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := 1990344704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := -15627010048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := 81840455680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := -296300855296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := 106883039232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := -1299848249344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := 1527105634304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := -1391830548480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := 1862160924672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := -3358378278912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := 3765472247808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := -1497068519424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := -561698521088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := 37325586432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := -4145152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := 6815744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := -191332352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := -845086720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := 1954267136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := -10641014784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := 232098037760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := -446640160768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := 75947098112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := -27337818112, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := 703838060544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := -83299860480, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := 1556488110080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := -72022294528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := -5010358272, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := -2850816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r454 : ℚ := { num := 68321280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r455 : ℚ := { num := -788922368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r456 : ℚ := { num := 5242257408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r457 : ℚ := { num := -3083763712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r458 : ℚ := { num := 56047206400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r459 : ℚ := { num := -1801977856, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r460 : ℚ := { num := 75780161536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r461 : ℚ := { num := -43715035136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r462 : ℚ := { num := 102637207552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r463 : ℚ := { num := -29982851072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r464 : ℚ := { num := 127140855808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r465 : ℚ := { num := 7876149248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r466 : ℚ := { num := -456032256, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r467 : ℚ := { num := 1769472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r468 : ℚ := { num := -205389824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r469 : ℚ := { num := 1737949184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r470 : ℚ := { num := -8605532160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r471 : ℚ := { num := 90308608, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r472 : ℚ := { num := -6784548864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r473 : ℚ := { num := 47415427072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r474 : ℚ := { num := -30221008896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r475 : ℚ := { num := 64897482752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r476 : ℚ := { num := -141895794688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r477 : ℚ := { num := 100758388736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r478 : ℚ := { num := 2509111296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r479 : ℚ := { num := -16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r480 : ℚ := { num := -10354688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r481 : ℚ := { num := 7356416, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r482 : ℚ := { num := -68976640, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r483 : ℚ := { num := 8616361984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r484 : ℚ := { num := -48372088832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r485 : ℚ := { num := 203118886912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r486 : ℚ := { num := -628276789248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r487 : ℚ := { num := 1407217254400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r488 : ℚ := { num := -2239009619968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r489 : ℚ := { num := 2599019003904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r490 : ℚ := { num := -2987934318592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r491 : ℚ := { num := 5354845093888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r492 : ℚ := { num := -9609334915072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r493 : ℚ := { num := 1510885638144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r494 : ℚ := { num := -4743510409216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r495 : ℚ := { num := -226958426112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r496 : ℚ := { num := 37529026560, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r497 : ℚ := { num := 98304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r498 : ℚ := { num := -41156608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r499 : ℚ := { num := 94470144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r500 : ℚ := { num := -5667389440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r501 : ℚ := { num := 620527616, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r502 : ℚ := { num := -15583150080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r503 : ℚ := { num := 269468467200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r504 : ℚ := { num := -9522282496, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r505 : ℚ := { num := 5003051008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r506 : ℚ := { num := -38986055680, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r507 : ℚ := { num := 769878360064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r508 : ℚ := { num := -103401357312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r509 : ℚ := { num := 38485524480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r510 : ℚ := { num := -298844160, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r511 : ℚ := { num := 11309383680, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r512 : ℚ := { num := -14746124288, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r513 : ℚ := { num := 16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r514 : ℚ := { num := -32768, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r515 : ℚ := { num := 180224, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r516 : ℚ := { num := -96534528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r517 : ℚ := { num := 846217216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r518 : ℚ := { num := -5833785344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r519 : ℚ := { num := 29677502464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r520 : ℚ := { num := -15281618944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r521 : ℚ := { num := 265608282112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r522 : ℚ := { num := -439491330048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r523 : ℚ := { num := 480811040768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r524 : ℚ := { num := -481681145856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r525 : ℚ := { num := 127687278592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r526 : ℚ := { num := -1628432596992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r527 : ℚ := { num := 1527588339712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r528 : ℚ := { num := -50725191680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r529 : ℚ := { num := -5376442368, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r530 : ℚ := { num := 491520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r531 : ℚ := { num := -38830080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r532 : ℚ := { num := 253558784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r533 : ℚ := { num := -1069744128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r534 : ℚ := { num := 2959966208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r535 : ℚ := { num := -4541743104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r536 : ℚ := { num := -1675755520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r537 : ℚ := { num := 1670643712, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r538 : ℚ := { num := -66056126464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r539 : ℚ := { num := 43333746688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r540 : ℚ := { num := 96622411776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r541 : ℚ := { num := -188662874112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r542 : ℚ := { num := 19759104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r543 : ℚ := { num := 190939136, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r544 : ℚ := { num := -9732096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r545 : ℚ := { num := 153288704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r546 : ℚ := { num := -1347682304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r547 : ℚ := { num := 1046085632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r548 : ℚ := { num := -25602654208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r549 : ℚ := { num := 57371852800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r550 : ℚ := { num := -77299908608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r551 : ℚ := { num := 52759625728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r552 : ℚ := { num := -3646717952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r553 : ℚ := { num := 94939447296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r554 : ℚ := { num := -205027409920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r555 : ℚ := { num := 18499108864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r556 : ℚ := { num := 2335014912, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r557 : ℚ := { num := -4924702720, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r558 : ℚ := { num := 3625517056, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r559 : ℚ := { num := 28180480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r560 : ℚ := { num := -195493888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r561 : ℚ := { num := 36372480, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r562 : ℚ := { num := 612564992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r563 : ℚ := { num := -13598195712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r564 : ℚ := { num := 7955939328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r565 : ℚ := { num := -114251333632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r566 : ℚ := { num := 115685588992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r567 : ℚ := { num := -55947952128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r568 : ℚ := { num := 132208459776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r569 : ℚ := { num := -354294104064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r570 : ℚ := { num := 5768675328, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r571 : ℚ := { num := 397934592, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r572 : ℚ := { num := -393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r573 : ℚ := { num := 10289152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r574 : ℚ := { num := -15663104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r575 : ℚ := { num := 86966272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r576 : ℚ := { num := -1792212992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r577 : ℚ := { num := 2014969856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r578 : ℚ := { num := 3122528256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r579 : ℚ := { num := -11618615296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r580 : ℚ := { num := 7292583936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r581 : ℚ := { num := 8775073792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r582 : ℚ := { num := 7330267136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r583 : ℚ := { num := -7845773312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r584 : ℚ := { num := 57475072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r585 : ℚ := { num := -65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r586 : ℚ := { num := 1966080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r587 : ℚ := { num := -196608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r588 : ℚ := { num := 139591680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r589 : ℚ := { num := -59506688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r590 : ℚ := { num := 373030912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r591 : ℚ := { num := 68550656, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r592 : ℚ := { num := -3108765696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r593 : ℚ := { num := 706150400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r594 : ℚ := { num := 415891456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r595 : ℚ := { num := 3342794752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r596 : ℚ := { num := -1047134208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r597 : ℚ := { num := -1179648, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r598 : ℚ := { num := -11665408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r599 : ℚ := { num := 99221504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r600 : ℚ := { num := -56098816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r601 : ℚ := { num := 571998208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r602 : ℚ := { num := 763625472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r603 : ℚ := { num := -3165913088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r604 : ℚ := { num := 947388416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r605 : ℚ := { num := 214958080, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r606 : ℚ := { num := 4296933376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r607 : ℚ := { num := -92930048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r608 : ℚ := { num := 25165824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r609 : ℚ := { num := -12582912, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r610 : ℚ := { num := 679477248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r611 : ℚ := { num := 211812352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r612 : ℚ := { num := -5259657216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r613 : ℚ := { num := 6127878144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r614 : ℚ := { num := 75497472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r615 : ℚ := { num := 294912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r616 : ℚ := { num := -8896512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r617 : ℚ := { num := 118407168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r618 : ℚ := { num := -932659200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r619 : ℚ := { num := 4877991936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r620 : ℚ := { num := -2524004352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r621 : ℚ := { num := 42838769664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r622 : ℚ := { num := -52992294912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r623 : ℚ := { num := -57179357184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r624 : ℚ := { num := 59598520320, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r625 : ℚ := { num := -830143709184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r626 : ℚ := { num := 458777837568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r627 : ℚ := { num := 1208600543232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r628 : ℚ := { num := -346325630976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r629 : ℚ := { num := 11030839296, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r630 : ℚ := { num := 55482728448, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r631 : ℚ := { num := -2921447424, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r632 : ℚ := { num := 8110080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r633 : ℚ := { num := -67600384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r634 : ℚ := { num := 364101632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r635 : ℚ := { num := -191201280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r636 : ℚ := { num := 3321348096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r637 : ℚ := { num := -4554850304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r638 : ℚ := { num := -2472525824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r639 : ℚ := { num := 28523790336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r640 : ℚ := { num := -64134234112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r641 : ℚ := { num := 61595549696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r642 : ℚ := { num := 6022184960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r643 : ℚ := { num := -1418690560, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r644 : ℚ := { num := 2250457088, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r645 : ℚ := { num := -5970886656, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r646 : ℚ := { num := 412647424, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r647 : ℚ := { num := -18153472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r648 : ℚ := { num := 267190272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r649 : ℚ := { num := -313131008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r650 : ℚ := { num := 10991108096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r651 : ℚ := { num := -34079965184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r652 : ℚ := { num := 58061881344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r653 : ℚ := { num := -10783817728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r654 : ℚ := { num := -27593670656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r655 : ℚ := { num := 26992771072, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r656 : ℚ := { num := -473908051968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r657 : ℚ := { num := 156337045504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r658 : ℚ := { num := 12698583040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r659 : ℚ := { num := -59572224, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r660 : ℚ := { num := -9895936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r661 : ℚ := { num := 156041216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r662 : ℚ := { num := -4653056, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r663 : ℚ := { num := 986644480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r664 : ℚ := { num := -21126578176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r665 : ℚ := { num := 32814792704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r666 : ℚ := { num := 5505679360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r667 : ℚ := { num := -18951831552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r668 : ℚ := { num := 37390319616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r669 : ℚ := { num := -4438032384, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r670 : ℚ := { num := 518848512, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r671 : ℚ := { num := 67436544, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r672 : ℚ := { num := 16318464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r673 : ℚ := { num := -203948032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r674 : ℚ := { num := 186187776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r675 : ℚ := { num := -4410310656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r676 : ℚ := { num := 937820160, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r677 : ℚ := { num := 3730833408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r678 : ℚ := { num := -108134400, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r679 : ℚ := { num := 6905397248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r680 : ℚ := { num := -453181440, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r681 : ℚ := { num := -267911168, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r682 : ℚ := { num := 9633792, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r683 : ℚ := { num := 131072, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r684 : ℚ := { num := -110362624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r685 : ℚ := { num := 912785408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r686 : ℚ := { num := -3945529344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r687 : ℚ := { num := 8214282240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r688 : ℚ := { num := -1825570816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r689 : ℚ := { num := -28260696064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r690 : ℚ := { num := 3290300416, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r691 : ℚ := { num := -4649517056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r692 : ℚ := { num := -7077888, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r693 : ℚ := { num := 3801088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r694 : ℚ := { num := -44236800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r695 : ℚ := { num := 265682944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r696 : ℚ := { num := -123011072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r697 : ℚ := { num := 1207173120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r698 : ℚ := { num := 1257373696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r699 : ℚ := { num := -8286109696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r700 : ℚ := { num := 14278983680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r701 : ℚ := { num := -1442971648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r702 : ℚ := { num := -10317922304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r703 : ℚ := { num := 6595674112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r704 : ℚ := { num := -55771136, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r705 : ℚ := { num := -6291456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r706 : ℚ := { num := 3145728, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r707 : ℚ := { num := -169869312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r708 : ℚ := { num := -52953088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r709 : ℚ := { num := 1314914304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r710 : ℚ := { num := -1531969536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r711 : ℚ := { num := -18874368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r712 : ℚ := { num := 1572864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r713 : ℚ := { num := -34996224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r714 : ℚ := { num := 297664512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r715 : ℚ := { num := -168296448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r716 : ℚ := { num := 1715994624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r717 : ℚ := { num := 2290876416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r718 : ℚ := { num := -9497739264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r719 : ℚ := { num := 2842165248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r720 : ℚ := { num := 644874240, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r721 : ℚ := { num := 12890800128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r722 : ℚ := { num := -278790144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r723 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r724 : ℚ := { num := 1, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19],[0,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38],[0,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56],[0,r57,r58,r59,r60,r61,r62,r63,r64,r65,r66,r67,r68,r69,r70,r71,r72,r73],[0,r0,r74,r75,r76,r77,r78,r79,r80,r81,r82,r83,r84,r85,r86,r87,r88],[0,r89,r90,r91,r92,r93,r94,r95,r96,r97,r98,r99,r100,r101,r102,r103],[0,0,r39,r104,r105,r106,r107,r108,r109,r110,r111,r112,r113,r114,r115],[],[],[],[],[],[],[r116,r117,r118,r119,r120,r121,r122,r123,r124,r125,r126,r127,r128,r129,r130,r131,r132,r133,r134],[0,r89,r135,r136,r137,r138,r139,r140,r141,r142,r143,r144,r145,r146,r147,r148,r149,r150],[r151,r152,r153,r154,r155,r156,r157,r158,r159,r160,r161,r162,r163,r164,r165,r166,r167],[0,r168,r169,r170,r171,r172,r173,r174,r175,r176,r177,r178,r179,r180,r181,r182],[],[],[],[],[],[],[],[0,r183,r184,r185,r186,r187,r188,r189,r190,r191,r192,r193,r194,r195,r196,r197,r198],[0,r89,r90,r91,r92,r93,r94,r95,r96,r97,r98,r99,r100,r101,r102,r103],[],[],[],[],[],[],[],[r20,r199,r200,r201,r202,r203,r204,r205,r206,r207,r208,r209,r210,r211,r212],[0,r213,r214,r215,r216,r217,r218,r219,r220,r221,r222,r223,r224,r225],[r226,r227,r228,r229,r230,r231,r232,r233,r234,r235,r236,r237,r238],[0,r239,r240,r241,r242,r243,r244,r245,r246,r247,r248,r249],[],[],[],[0,0,0,0,r250,r251,r252,r253,r254,r255,r256,r257,-2097152],[],[],[],[],[],[],[],[],[0,r258,r259,r260,r261,r262,r263,r264,r265,r266,r267,r268,r269,r270,r271,r272,r273,r274],[r151,r152,r275,r276,r277,r278,r279,r280,r281,r282,r283,r284,r285,r286,r287,r288,r289],[0,r168,r169,r170,r171,r172,r173,r174,r175,r176,r177,r178,r179,r180,r181,r182],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,r213,r214,r215,r216,r217,r218,r219,r220,r221,r222,r223,r224,r225],[0,0,0,0,r250,r251,r252,r253,r254,r255,r256,r257,-2097152],[],[],[],[],[],[],[],[],[],[],[0,r239,r290,r291,r292,r293,r294,r295,r296,r297,r298,r299,r300,r301,r302],[0,r183,r303,r304,r305,r306,r307,r308,r309,r310,r311,r312,r313,r314],[0,r315,r316,r317,r318,r319,r320,r321,r322,r323,r324,r325,r326],[0,r168,r327,r328,r329,r330,r331,r332,r333,r334,r335,r336],[],[],[],[r168,r337,r338,r339,r340,r341,r342,r343,r344,r345,r346,r347,r348],[],[],[],[],[],[],[],[r183,r349,r350,r351,r352,r353,r354,r355,524288],[0,r356,r357,r358,r359,r360,r361,r362,r363,r364,r365,r366],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r20,r367,r368,r369,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382,r383,r384,r385]),(⟨0,0,1⟩,[0,r89,r386,r387,r388,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398,r399,r400,r401,r402,r403]),(⟨0,0,2⟩,[0,r168,r404,r405,r406,r407,r408,r409,r410,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420]),(⟨0,0,3⟩,[0,r421,r422,r423,r424,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434,r435,r436,r437]),(⟨0,0,4⟩,[0,r20,r438,r439,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451,r452]),(⟨0,0,5⟩,[0,r151,r453,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466]),(⟨0,0,6⟩,[0,0,r168,r467,r468,r469,r470,r471,r472,r473,r474,r475,r476,r477,r478]),(⟨0,1,0⟩,[0,r89,r386,r387,r388,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398,r399,r400,r401,r402,r403]),(⟨0,1,1⟩,[r479,r258,r480,r481,r482,r483,r484,r485,r486,r487,r488,r489,r490,r491,r492,r493,r494,r495,r496]),(⟨0,1,2⟩,[0,r151,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508,r509,r510,r511,r512]),(⟨0,1,3⟩,[r513,r514,r515,r516,r517,r518,r519,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529]),(⟨0,1,4⟩,[0,r226,r530,r531,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543]),(⟨0,2,0⟩,[0,r168,r404,r405,r406,r407,r408,r409,r410,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420]),(⟨0,2,1⟩,[0,r151,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508,r509,r510,r511,r512]),(⟨0,2,2⟩,[0,r0,r544,r545,r546,r547,r548,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558]),(⟨0,2,3⟩,[0,r151,r453,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466]),(⟨0,3,0⟩,[0,r421,r422,r423,r424,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434,r435,r436,r437]),(⟨0,3,1⟩,[r513,r514,r515,r516,r517,r518,r519,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529]),(⟨0,3,2⟩,[0,r151,r453,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466]),(⟨0,3,3⟩,[r89,r250,r559,r560,r561,r562,r563,r564,r565,r566,r567,r568,r569,r570,r571]),(⟨0,3,4⟩,[0,r572,r573,r574,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584]),(⟨0,3,5⟩,[r585,r586,r587,r588,r589,r590,r591,r592,r593,r594,r595,r596,r597]),(⟨0,3,6⟩,[0,r183,r598,r599,r600,r601,r602,r603,r604,r605,r606,r607]),(⟨0,4,0⟩,[0,r20,r438,r439,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451,r452]),(⟨0,4,1⟩,[0,r226,r530,r531,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543]),(⟨0,4,3⟩,[0,r572,r573,r574,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584]),(⟨0,4,4⟩,[0,0,0,0,r315,r608,r609,r610,r611,r612,r613,r614,-1048576]),(⟨0,5,0⟩,[0,r151,r453,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466]),(⟨0,5,3⟩,[r585,r586,r587,r588,r589,r590,r591,r592,r593,r594,r595,r596,r597]),(⟨0,6,0⟩,[0,0,r168,r467,r468,r469,r470,r471,r472,r473,r474,r475,r476,r477,r478]),(⟨0,6,3⟩,[0,r183,r598,r599,r600,r601,r602,r603,r604,r605,r606,r607]),(⟨1,0,0⟩,[0,r89,r386,r387,r388,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398,r399,r400,r401,r402,r403]),(⟨1,0,1⟩,[r479,r258,r480,r481,r482,r483,r484,r485,r486,r487,r488,r489,r490,r491,r492,r493,r494,r495,r496]),(⟨1,0,2⟩,[0,r151,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508,r509,r510,r511,r512]),(⟨1,0,3⟩,[r513,r514,r515,r516,r517,r518,r519,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529]),(⟨1,0,4⟩,[0,r226,r530,r531,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543]),(⟨1,1,0⟩,[r479,r258,r480,r481,r482,r483,r484,r485,r486,r487,r488,r489,r490,r491,r492,r493,r494,r495,r496]),(⟨1,1,1⟩,[0,r615,r616,r617,r618,r619,r620,r621,r622,r623,r624,r625,r626,r627,r628,r629,r630,r631]),(⟨1,1,2⟩,[r513,r514,r632,r633,r634,r635,r636,r637,r638,r639,r640,r641,r642,r643,r644,r645,r646]),(⟨1,1,3⟩,[0,r226,r530,r531,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543]),(⟨1,2,0⟩,[0,r151,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508,r509,r510,r511,r512]),(⟨1,2,1⟩,[r513,r514,r632,r633,r634,r635,r636,r637,r638,r639,r640,r641,r642,r643,r644,r645,r646]),(⟨1,3,0⟩,[r513,r514,r515,r516,r517,r518,r519,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529]),(⟨1,3,1⟩,[0,r226,r530,r531,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543]),(⟨1,3,3⟩,[0,r572,r573,r574,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584]),(⟨1,3,4⟩,[0,0,0,0,r315,r608,r609,r610,r611,r612,r613,r614,-1048576]),(⟨1,4,0⟩,[0,r226,r530,r531,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543]),(⟨1,4,3⟩,[0,0,0,0,r315,r608,r609,r610,r611,r612,r613,r614,-1048576]),(⟨2,0,0⟩,[0,r168,r404,r405,r406,r407,r408,r409,r410,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420]),(⟨2,0,1⟩,[0,r151,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508,r509,r510,r511,r512]),(⟨2,0,2⟩,[0,r0,r544,r545,r546,r547,r548,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558]),(⟨2,0,3⟩,[0,r151,r453,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466]),(⟨2,1,0⟩,[0,r151,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508,r509,r510,r511,r512]),(⟨2,1,1⟩,[r513,r514,r632,r633,r634,r635,r636,r637,r638,r639,r640,r641,r642,r643,r644,r645,r646]),(⟨2,2,0⟩,[0,r0,r544,r545,r546,r547,r548,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558]),(⟨2,2,2⟩,[0,r183,r647,r648,r649,r650,r651,r652,r653,r654,r655,r656,r657,r658,r659]),(⟨2,2,3⟩,[0,r0,r660,r661,r662,r663,r664,r665,r666,r667,r668,r669,r670,r671]),(⟨2,2,4⟩,[0,r39,r672,r673,r674,r675,r676,r677,r678,r679,r680,r681,r682]),(⟨2,2,5⟩,[0,r226,r683,r684,r685,r686,r687,r688,r689,r690,r691,r692]),(⟨2,3,0⟩,[0,r151,r453,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466]),(⟨2,3,2⟩,[0,r0,r660,r661,r662,r663,r664,r665,r666,r667,r668,r669,r670,r671]),(⟨2,3,3⟩,[r226,r693,r694,r695,r696,r697,r698,r699,r700,r701,r702,r703,r704]),(⟨2,4,2⟩,[0,r39,r672,r673,r674,r675,r676,r677,r678,r679,r680,r681,r682]),(⟨2,5,2⟩,[0,r226,r683,r684,r685,r686,r687,r688,r689,r690,r691,r692]),(⟨2,5,5⟩,[r0,r705,r706,r707,r708,r709,r710,r711,262144]),(⟨3,0,0⟩,[0,r421,r422,r423,r424,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434,r435,r436,r437]),(⟨3,0,1⟩,[r513,r514,r515,r516,r517,r518,r519,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529]),(⟨3,0,2⟩,[0,r151,r453,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466]),(⟨3,0,3⟩,[r89,r250,r559,r560,r561,r562,r563,r564,r565,r566,r567,r568,r569,r570,r571]),(⟨3,0,4⟩,[0,r572,r573,r574,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584]),(⟨3,0,5⟩,[r585,r586,r587,r588,r589,r590,r591,r592,r593,r594,r595,r596,r597]),(⟨3,0,6⟩,[0,r183,r598,r599,r600,r601,r602,r603,r604,r605,r606,r607]),(⟨3,1,0⟩,[r513,r514,r515,r516,r517,r518,r519,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529]),(⟨3,1,1⟩,[0,r226,r530,r531,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543]),(⟨3,1,3⟩,[0,r572,r573,r574,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584]),(⟨3,1,4⟩,[0,0,0,0,r315,r608,r609,r610,r611,r612,r613,r614,-1048576]),(⟨3,2,0⟩,[0,r151,r453,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466]),(⟨3,2,2⟩,[0,r0,r660,r661,r662,r663,r664,r665,r666,r667,r668,r669,r670,r671]),(⟨3,2,3⟩,[r226,r693,r694,r695,r696,r697,r698,r699,r700,r701,r702,r703,r704]),(⟨3,3,0⟩,[r89,r250,r559,r560,r561,r562,r563,r564,r565,r566,r567,r568,r569,r570,r571]),(⟨3,3,1⟩,[0,r572,r573,r574,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584]),(⟨3,3,2⟩,[r226,r693,r694,r695,r696,r697,r698,r699,r700,r701,r702,r703,r704]),(⟨3,3,3⟩,[0,r712,r713,r714,r715,r716,r717,r718,r719,r720,r721,r722]),(⟨3,4,0⟩,[0,r572,r573,r574,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584]),(⟨3,4,1⟩,[0,0,0,0,r315,r608,r609,r610,r611,r612,r613,r614,-1048576]),(⟨3,5,0⟩,[r585,r586,r587,r588,r589,r590,r591,r592,r593,r594,r595,r596,r597]),(⟨3,6,0⟩,[0,r183,r598,r599,r600,r601,r602,r603,r604,r605,r606,r607]),(⟨4,0,0⟩,[0,r20,r438,r439,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451,r452]),(⟨4,0,1⟩,[0,r226,r530,r531,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543]),(⟨4,0,3⟩,[0,r572,r573,r574,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584]),(⟨4,0,4⟩,[0,0,0,0,r315,r608,r609,r610,r611,r612,r613,r614,-1048576]),(⟨4,1,0⟩,[0,r226,r530,r531,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543]),(⟨4,1,3⟩,[0,0,0,0,r315,r608,r609,r610,r611,r612,r613,r614,-1048576]),(⟨4,2,2⟩,[0,r39,r672,r673,r674,r675,r676,r677,r678,r679,r680,r681,r682]),(⟨4,3,0⟩,[0,r572,r573,r574,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584]),(⟨4,3,1⟩,[0,0,0,0,r315,r608,r609,r610,r611,r612,r613,r614,-1048576]),(⟨4,4,0⟩,[0,0,0,0,r315,r608,r609,r610,r611,r612,r613,r614,-1048576]),(⟨5,0,0⟩,[0,r151,r453,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466]),(⟨5,0,3⟩,[r585,r586,r587,r588,r589,r590,r591,r592,r593,r594,r595,r596,r597]),(⟨5,2,2⟩,[0,r226,r683,r684,r685,r686,r687,r688,r689,r690,r691,r692]),(⟨5,2,5⟩,[r0,r705,r706,r707,r708,r709,r710,r711,262144]),(⟨5,3,0⟩,[r585,r586,r587,r588,r589,r590,r591,r592,r593,r594,r595,r596,r597]),(⟨5,5,2⟩,[r0,r705,r706,r707,r708,r709,r710,r711,262144]),(⟨6,0,0⟩,[0,0,r168,r467,r468,r469,r470,r471,r472,r473,r474,r475,r476,r477,r478]),(⟨6,0,3⟩,[0,r183,r598,r599,r600,r601,r602,r603,r604,r605,r606,r607]),(⟨6,3,0⟩,[0,r183,r598,r599,r600,r601,r602,r603,r604,r605,r606,r607])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,-512,11584,-106560,532736,-1621824,3051904,-3282624,1363712,606272,-407232]),(⟨0,0,1⟩,[0,-256,6592,-65600,337472,-994752,1716288,-1563072,348096,460992]),(⟨0,0,2⟩,[0,512,-9792,66304,-201792,309760,-192192,-87808,65856]),(⟨0,0,3⟩,[0,128,-4736,47104,-188672,361600,-281728,-48384]),(⟨0,1,0⟩,[0,-256,6592,-65600,337472,-994752,1716288,-1563072,348096,460992]),(⟨0,1,1⟩,[64,-1024,6144,-20992,42368,-19456,-107520,326144,-373184]),(⟨0,2,0⟩,[0,512,-9792,66304,-201792,309760,-192192,-87808,65856]),(⟨0,3,0⟩,[0,128,-4736,47104,-188672,361600,-281728,-48384]),(⟨0,3,3⟩,[-256,3072,-7680,-9216,30464]),(⟨1,0,0⟩,[0,-256,6592,-65600,337472,-994752,1716288,-1563072,348096,460992]),(⟨1,0,1⟩,[64,-1024,6144,-20992,42368,-19456,-107520,326144,-373184]),(⟨1,1,0⟩,[64,-1024,6144,-20992,42368,-19456,-107520,326144,-373184]),(⟨2,0,0⟩,[0,512,-9792,66304,-201792,309760,-192192,-87808,65856]),(⟨3,0,0⟩,[0,128,-4736,47104,-188672,361600,-281728,-48384]),(⟨3,0,3⟩,[-256,3072,-7680,-9216,30464]),(⟨3,3,0⟩,[-256,3072,-7680,-9216,30464])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[-256,5120,-43008,199936,-545280,801024,-457728,253696,-1684736,2508544,-513024]),(⟨0,0,1⟩,[0,1536,-21760,121088,-327424,405248,-133888,235264,-1327360,1571584]),(⟨0,0,2⟩,[256,-4608,28416,-75264,67840,43520,25856,-250368,-32256]),(⟨0,0,3⟩,[0,-2048,20992,-74240,87040,37888,31232,-363008]),(⟨0,1,0⟩,[0,1536,-21760,121088,-327424,405248,-133888,235264,-1327360,1571584]),(⟨0,1,1⟩,[0,0,0,0,4096,-49152,122880,147456,-487424]),(⟨0,2,0⟩,[256,-4608,28416,-75264,67840,43520,25856,-250368,-32256]),(⟨0,3,0⟩,[0,-2048,20992,-74240,87040,37888,31232,-363008]),(⟨1,0,0⟩,[0,1536,-21760,121088,-327424,405248,-133888,235264,-1327360,1571584]),(⟨1,0,1⟩,[0,0,0,0,4096,-49152,122880,147456,-487424]),(⟨1,1,0⟩,[0,0,0,0,4096,-49152,122880,147456,-487424]),(⟨2,0,0⟩,[256,-4608,28416,-75264,67840,43520,25856,-250368,-32256]),(⟨2,2,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨3,0,0⟩,[0,-2048,20992,-74240,87040,37888,31232,-363008])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 9 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r723) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 13 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r723) sourceRight))).isZero := by decide +kernel

noncomputable def partial16 : Poly := []

theorem partial_sound16 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 16)
      sourceRight).eval u v t=partial16.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨2,0,0⟩,[0,512,-9792,66304,-201792,309760,-192192,-87808,65856]),(⟨3,0,0⟩,[0,128,-4736,47104,-188672,361600,-281728,-48384]),(⟨3,0,3⟩,[-256,3072,-7680,-9216,30464]),(⟨3,3,0⟩,[-256,3072,-7680,-9216,30464])]

noncomputable def partial12 : Poly := [(⟨2,0,0⟩,[0,-131072,5128192,-89128960,914636800,-6201032704,29319905280,-98861416448,237487734784,-398554611712,459503550464,-422414188544,571626536960,-1017897402368,1151942836224,-476395700224,-232621096960,210250285056,-33785708544]),(⟨2,0,1⟩,[0,0,786432,-26181632,376913920,-3106062336,16309026816,-57216434176,135928037376,-216319574016,232811003904,-233506373632,413513662464,-735067521024,712446443520,-169999499264,-225412268032,103498235904]),(⟨2,0,2⟩,[0,131072,-4866048,76644352,-673972224,3664969728,-12843008000,28938108928,-39539015680,28048097280,-12579487744,37115035648,-75368038400,38722797568,29886431232,-13655900160,-2124251136]),(⟨2,0,3⟩,[0,0,-1048576,30801920,-379355136,2576646144,-10625712128,27293220864,-42394779648,37231591424,-27462139904,63112806400,-116042661888,69519966208,33931821056,-23906254848]),(⟨2,1,0⟩,[0,0,786432,-26181632,376913920,-3106062336,16309026816,-57216434176,135928037376,-216319574016,232811003904,-233506373632,413513662464,-735067521024,712446443520,-169999499264,-225412268032,103498235904]),(⟨2,1,1⟩,[0,0,0,0,0,2097152,-65273856,815792128,-5213257728,17641242624,-26258964480,-14923333632,125003366400,-193351122944,88823562240,52510588928,-32099794944]),(⟨2,2,0⟩,[0,131072,-4866048,76644352,-673972224,3664969728,-12843008000,28938108928,-39539015680,28048097280,-12579487744,37115035648,-75368038400,38722797568,29886431232,-13655900160,-2124251136]),(⟨2,3,0⟩,[0,0,-1048576,30801920,-379355136,2576646144,-10625712128,27293220864,-42394779648,37231591424,-27462139904,63112806400,-116042661888,69519966208,33931821056,-23906254848]),(⟨3,0,0⟩,[0,-32768,2654208,-67993600,895664128,-7207174144,38449709056,-141457620992,362904502272,-641848262656,773018779648,-737478148096,1033902833664,-1891052109824,2178691694592,-980721795072,-202252435456,128320389120]),(⟨3,0,1⟩,[0,0,196608,-10059776,190906368,-1928069120,11901927424,-47690645504,126156996608,-217866043392,249494831104,-276019576832,552650866688,-1029640814592,1019679801344,-326025641984,-108139315200]),(⟨3,0,2⟩,[0,32768,-1802240,37519360,-409567232,2665611264,-10960633856,28753985536,-45902135296,38548570112,-16252895232,39524401152,-93837295616,57620889600,21201223680,1560674304]),(⟨3,0,3⟩,[65536,-2097152,28442624,-207880192,823721984,-1125384192,-4992663552,29592387584,-66759491584,68270161920,-25726943232,67310977024,-212398309376,181906702336,1935015936]),(⟨3,0,4⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨3,0,5⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨3,0,6⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨3,1,0⟩,[0,0,196608,-10059776,190906368,-1928069120,11901927424,-47690645504,126156996608,-217866043392,249494831104,-276019576832,552650866688,-1029640814592,1019679801344,-326025641984,-108139315200]),(⟨3,1,1⟩,[0,0,0,0,0,524288,-25690112,441450496,-3651141632,15782117376,-32857128960,7302283264,113042784256,-223740428288,130186477568,23583522816]),(⟨3,1,3⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨3,1,4⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨3,2,0⟩,[0,32768,-1802240,37519360,-409567232,2665611264,-10960633856,28753985536,-45902135296,38548570112,-16252895232,39524401152,-93837295616,57620889600,21201223680,1560674304]),(⟨3,2,3⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨3,3,0⟩,[65536,-2097152,28442624,-207880192,823721984,-1125384192,-4992663552,29592387584,-66759491584,68270161920,-25726943232,67310977024,-212398309376,181906702336,1935015936]),(⟨3,3,1⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨3,3,2⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨3,3,3⟩,[0,1048576,-23330816,198443008,-785383424,1143996416,1527250944,-6331826176,1894776832,7308574720,8593866752,-22117351424]),(⟨3,4,0⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨3,4,1⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨3,5,0⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨3,6,0⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨4,0,0⟩,[0,131072,-4669440,66584576,-483065856,1734803456,-875806720,-19568328704,91831238656,-207459188736,263174307840,-223981207552,352279461888,-797566894080,960742670336,-392192131072,-78163771392]),(⟨4,0,1⟩,[0,0,0,0,0,524288,-25690112,441450496,-3651141632,15782117376,-32857128960,7302283264,113042784256,-223740428288,130186477568,23583522816]),(⟨4,0,3⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨4,0,4⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨4,1,0⟩,[0,0,0,0,0,524288,-25690112,441450496,-3651141632,15782117376,-32857128960,7302283264,113042784256,-223740428288,130186477568,23583522816]),(⟨4,1,3⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨4,2,2⟩,[0,-524288,16318464,-203948032,1303314432,-4410310656,6564741120,3730833408,-31250841600,48337780736,-22205890560,-13127647232,8024948736]),(⟨4,3,0⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨4,3,1⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨4,4,0⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨5,0,0⟩,[0,32768,-2850816,68321280,-788922368,5242257408,-21586345984,56047206400,-88296914944,75780161536,-43715035136,102637207552,-209879957504,127140855808,55133044736,-22345580544]),(⟨5,0,3⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨5,2,2⟩,[0,-131072,6422528,-110362624,912785408,-3945529344,8214282240,-1825570816,-28260696064,55935107072,-32546619392,-5895880704]),(⟨5,2,5⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨5,3,0⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨5,5,2⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨6,0,0⟩,[0,0,-262144,12386304,-205389824,1737949184,-8605532160,26099187712,-47491842048,47415427072,-30221008896,64897482752,-141895794688,100758388736,17563779072]),(⟨6,0,3⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨6,3,0⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial16)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 16))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound16 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨0,3,3⟩,[-256,3072,-7680,-9216,30464]),(⟨1,0,0⟩,[0,-256,6592,-65600,337472,-994752,1716288,-1563072,348096,460992]),(⟨1,0,1⟩,[64,-1024,6144,-20992,42368,-19456,-107520,326144,-373184]),(⟨1,1,0⟩,[64,-1024,6144,-20992,42368,-19456,-107520,326144,-373184])]

noncomputable def partial8 : Poly := [(⟨0,3,3⟩,[65536,-2097152,28704768,-220266496,1029111808,-2863333376,3612868608,3493199872,-19267649536,20854734848,4494065664,2413494272,-70502514688,81148313600,-15628763136]),(⟨0,3,4⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨0,3,5⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨0,3,6⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨0,4,3⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨0,4,4⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨0,5,3⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨0,6,3⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨1,0,0⟩,[0,65536,-2998272,61554688,-756957184,6261407744,-36961845248,160610533376,-520439087104,1256908750848,-2240663552000,2944997834752,-3124150321152,3734452994048,-5746615320576,7326380900352,-5271029858304,898457763840,977837113344,-236499959808]),(⟨1,0,1⟩,[-16384,589824,-9961472,109363200,-897400832,5790613504,-29367877632,114857132032,-338821103616,735673434112,-1144349540352,1281822834688,-1324620955648,2128279977984,-3704833753088,3888344088576,-1308069396480,-1168308420608,915939999744]),(⟨1,0,2⟩,[0,32768,-98304,-14974976,284377088,-2560278528,14057242624,-51241451520,128161497088,-222646222848,278045753344,-297997402112,378387415040,-519393263616,603881177088,-714498211840,881266376704,-601359761408]),(⟨1,0,3⟩,[16384,-557056,8634368,-86474752,655310848,-3905716224,17775575040,-59280687104,139451285504,-221625286656,231316209664,-205661569024,341160083456,-598791782400,507908538368,-29050699776,-155306360832]),(⟨1,0,4⟩,[0,-131072,3440640,-38830080,253558784,-1070268416,2985656320,-4983193600,1975386112,12618825728,-33198997504,36031463424,-16420372480,35077554176,-130048163840,135468777472]),(⟨1,1,0⟩,[-16384,589824,-9961472,109363200,-897400832,5790613504,-29367877632,114857132032,-338821103616,735673434112,-1144349540352,1281822834688,-1324620955648,2128279977984,-3704833753088,3888344088576,-1308069396480,-1168308420608,915939999744]),(⟨1,1,1⟩,[0,196608,-5931008,78938112,-621772800,3253043200,-11818270720,29183344640,-40707129344,-10493526016,193620115456,-422169968640,327874609152,275082412032,-569257328640,-509513596928,1914130104320,-1397678571520]),(⟨1,1,2⟩,[16384,-557056,8110080,-67600384,363839488,-1333166080,3303260160,-4866277376,962609152,14219116544,-37507219456,55809507328,-64689848320,71787118592,-33194033152,-131085402112,193936261120]),(⟨1,1,3⟩,[0,-131072,3440640,-38830080,253558784,-1070268416,2985656320,-4983193600,1975386112,12618825728,-33198997504,36031463424,-16420372480,35077554176,-130048163840,135468777472]),(⟨1,2,0⟩,[0,32768,-98304,-14974976,284377088,-2560278528,14057242624,-51241451520,128161497088,-222646222848,278045753344,-297997402112,378387415040,-519393263616,603881177088,-714498211840,881266376704,-601359761408]),(⟨1,2,1⟩,[16384,-557056,8110080,-67600384,363839488,-1333166080,3303260160,-4866277376,962609152,14219116544,-37507219456,55809507328,-64689848320,71787118592,-33194033152,-131085402112,193936261120]),(⟨1,3,0⟩,[16384,-557056,8634368,-86474752,655310848,-3905716224,17775575040,-59280687104,139451285504,-221625286656,231316209664,-205661569024,341160083456,-598791782400,507908538368,-29050699776,-155306360832]),(⟨1,3,1⟩,[0,-131072,3440640,-38830080,253558784,-1070268416,2985656320,-4983193600,1975386112,12618825728,-33198997504,36031463424,-16420372480,35077554176,-130048163840,135468777472]),(⟨1,3,3⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨1,3,4⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨1,4,0⟩,[0,-131072,3440640,-38830080,253558784,-1070268416,2985656320,-4983193600,1975386112,12618825728,-33198997504,36031463424,-16420372480,35077554176,-130048163840,135468777472]),(⟨1,4,3⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨2,0,0⟩,[0,-131072,4734976,-73433088,639434752,-3373187072,10243080192,-9530900480,-60735619072,316953640960,-771476389888,1127029506048,-1134822096896,1436044935168,-2917049892864,4315827470336,-3042713927680,145410048000,690701942784]),(⟨2,0,1⟩,[0,98304,-2179072,13287424,66027520,-1480065024,10419683328,-42936844288,118263939072,-235379359744,371874217984,-510220943360,566439608320,-332200673280,-95646695424,10170875904,680805629952,-707690332160]),(⟨2,0,2⟩,[0,131072,-4866048,76644352,-673710080,3657629696,-12759646208,28433743872,-37760892928,24711528448,-12947537920,57824411648,-129659371520,90770964480,84529299456,-227654533120,179774586880]),(⟨2,0,3⟩,[0,0,-1048576,30801920,-379355136,2576646144,-10625712128,27293220864,-42394779648,37231591424,-27462139904,63112806400,-116042661888,69519966208,33931821056,-23906254848]),(⟨2,1,0⟩,[0,98304,-2179072,13287424,66027520,-1480065024,10419683328,-42936844288,118263939072,-235379359744,371874217984,-510220943360,566439608320,-332200673280,-95646695424,10170875904,680805629952,-707690332160]),(⟨2,1,1⟩,[0,0,0,0,524288,-12582912,101449728,-192937984,-1657012224,10968104960,-26995064832,26495418368,16420700160,-89254789120,198109298688,-375486676992,331697881088]),(⟨2,2,0⟩,[0,131072,-4866048,76644352,-673710080,3657629696,-12759646208,28433743872,-37760892928,24711528448,-12947537920,57824411648,-129659371520,90770964480,84529299456,-227654533120,179774586880]),(⟨2,3,0⟩,[0,0,-1048576,30801920,-379355136,2576646144,-10625712128,27293220864,-42394779648,37231591424,-27462139904,63112806400,-116042661888,69519966208,33931821056,-23906254848]),(⟨2,3,3⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨2,5,5⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨3,0,0⟩,[0,-98304,5521408,-122437632,1490927616,-11394498560,58435878912,-207602827264,514109030400,-873060745216,996507631616,-890020151296,1237341585408,-2282660937728,2543737061376,-1005536034816,-328898265088,113450631168]),(⟨3,0,1⟩,[16384,-557056,8306688,-77660160,554483712,-3253895168,15121825792,-52052557824,125341483008,-200310358016,212355661824,-240919445504,542252351488,-1009901862912,931842899968,-243112411136,-96101892096]),(⟨3,0,2⟩,[0,32768,-1802240,37519360,-409567232,2665611264,-10960633856,28753985536,-45902135296,38548570112,-16252895232,39524401152,-93837295616,57620889600,21201223680,1560674304]),(⟨3,0,3⟩,[65536,-2097152,28442624,-207880192,823721984,-1125384192,-4992663552,29592387584,-66759491584,68270161920,-25726943232,67310977024,-212398309376,181906702336,1935015936]),(⟨3,0,4⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨3,0,5⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨3,0,6⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨3,1,0⟩,[16384,-557056,8306688,-77660160,554483712,-3253895168,15121825792,-52052557824,125341483008,-200310358016,212355661824,-240919445504,542252351488,-1009901862912,931842899968,-243112411136,-96101892096]),(⟨3,1,1⟩,[0,0,0,0,0,524288,-25690112,441450496,-3651141632,15782117376,-32857128960,7302283264,113042784256,-223740428288,130186477568,23583522816]),(⟨3,1,3⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨3,1,4⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨3,2,0⟩,[0,32768,-1802240,37519360,-409567232,2665611264,-10960633856,28753985536,-45902135296,38548570112,-16252895232,39524401152,-93837295616,57620889600,21201223680,1560674304]),(⟨3,2,2⟩,[0,262144,-9895936,156041216,-1344733184,6906511360,-21126578176,32814792704,5505679360,-132662820864,261732237312,-217463586816,25423577088,56174641152]),(⟨3,2,3⟩,[-131072,3801088,-44236800,265682944,-861077504,1207173120,1257373696,-8286109696,14278983680,-10100801536,-10317922304,46169718784,-46457356288]),(⟨3,3,0⟩,[65536,-2097152,28442624,-207880192,823721984,-1125384192,-4992663552,29592387584,-66759491584,68270161920,-25726943232,67310977024,-212398309376,181906702336,1935015936]),(⟨3,3,1⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨3,3,2⟩,[-131072,3801088,-44236800,265682944,-861077504,1207173120,1257373696,-8286109696,14278983680,-10100801536,-10317922304,46169718784,-46457356288]),(⟨3,3,3⟩,[0,1572864,-34996224,297664512,-1178075136,1715994624,2290876416,-9497739264,2842165248,10962862080,12890800128,-33176027136]),(⟨3,4,0⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨3,4,1⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨3,5,0⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨3,6,0⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨4,0,0⟩,[0,131072,-4145152,47710208,-191332352,-845086720,13679869952,-74487103488,232098037760,-446640160768,531629686784,-464742907904,703838060544,-1416097628160,1556488110080,-504156061696,-245507555328]),(⟨4,0,1⟩,[0,-131072,3440640,-38830080,253558784,-1069744128,2959966208,-4541743104,-1675755520,28400943104,-66056126464,43333746688,96622411776,-188662874112,138313728,159052300288]),(⟨4,0,3⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨4,0,4⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨4,1,0⟩,[0,-131072,3440640,-38830080,253558784,-1069744128,2959966208,-4541743104,-1675755520,28400943104,-66056126464,43333746688,96622411776,-188662874112,138313728,159052300288]),(⟨4,1,3⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨4,2,2⟩,[0,-524288,16318464,-203948032,1303314432,-4410310656,6564741120,3730833408,-31250841600,48337780736,-22205890560,-13127647232,8024948736]),(⟨4,3,0⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨4,3,1⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨4,4,0⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨5,0,0⟩,[0,32768,-2850816,68321280,-788922368,5242257408,-21586345984,56047206400,-88296914944,75780161536,-43715035136,102637207552,-209879957504,127140855808,55133044736,-22345580544]),(⟨5,0,3⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨5,2,2⟩,[0,-131072,6422528,-110362624,912785408,-3945529344,8214282240,-1825570816,-28260696064,55935107072,-32546619392,-5895880704]),(⟨5,2,5⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨5,3,0⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨5,5,2⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨6,0,0⟩,[0,0,-262144,12386304,-205389824,1737949184,-8605532160,26099187712,-47491842048,47415427072,-30221008896,64897482752,-141895794688,100758388736,17563779072]),(⟨6,0,3⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨6,3,0⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,1,0⟩,[0,-256,6592,-65600,337472,-994752,1716288,-1563072,348096,460992]),(⟨0,1,1⟩,[64,-1024,6144,-20992,42368,-19456,-107520,326144,-373184]),(⟨0,2,0⟩,[0,512,-9792,66304,-201792,309760,-192192,-87808,65856]),(⟨0,3,0⟩,[0,128,-4736,47104,-188672,361600,-281728,-48384])]

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[0,65536,-2998272,61554688,-756957184,6261407744,-36961845248,160610533376,-520439087104,1256908750848,-2240663552000,2944997834752,-3124150321152,3734452994048,-5746615320576,7326380900352,-5271029858304,898457763840,977837113344,-236499959808]),(⟨0,1,1⟩,[-16384,589824,-9961472,109363200,-897400832,5790613504,-29367877632,114857132032,-338821103616,735673434112,-1144349540352,1281822834688,-1324620955648,2128279977984,-3704833753088,3888344088576,-1308069396480,-1168308420608,915939999744]),(⟨0,1,2⟩,[0,32768,-98304,-14974976,284377088,-2560278528,14057242624,-51241451520,128161497088,-222646222848,278045753344,-297997402112,378387415040,-519393263616,603881177088,-714498211840,881266376704,-601359761408]),(⟨0,1,3⟩,[16384,-557056,8634368,-86474752,655310848,-3905716224,17775575040,-59280687104,139451285504,-221625286656,231316209664,-205661569024,341160083456,-598791782400,507908538368,-29050699776,-155306360832]),(⟨0,1,4⟩,[0,-131072,3440640,-38830080,253558784,-1070268416,2985656320,-4983193600,1975386112,12618825728,-33198997504,36031463424,-16420372480,35077554176,-130048163840,135468777472]),(⟨0,2,0⟩,[0,-131072,4734976,-73433088,639434752,-3373187072,10243080192,-9530900480,-60735619072,316953640960,-771476389888,1127029506048,-1134822096896,1436044935168,-2917049892864,4315827470336,-3042713927680,145410048000,690701942784]),(⟨0,2,1⟩,[0,98304,-2179072,13287424,66027520,-1480065024,10419683328,-42936844288,118263939072,-235379359744,371874217984,-510220943360,566439608320,-332200673280,-95646695424,10170875904,680805629952,-707690332160]),(⟨0,2,2⟩,[0,131072,-4866048,76644352,-673710080,3657629696,-12759646208,28433743872,-37760892928,24711528448,-12947537920,57824411648,-129659371520,90770964480,84529299456,-227654533120,179774586880]),(⟨0,2,3⟩,[0,0,-1048576,30801920,-379355136,2576646144,-10625712128,27293220864,-42394779648,37231591424,-27462139904,63112806400,-116042661888,69519966208,33931821056,-23906254848]),(⟨0,3,0⟩,[0,-98304,5521408,-122437632,1490927616,-11394498560,58435878912,-207602827264,514109030400,-873060745216,996507631616,-890020151296,1237341585408,-2282660937728,2543737061376,-1005536034816,-328898265088,113450631168]),(⟨0,3,1⟩,[16384,-557056,8306688,-77660160,554483712,-3253895168,15121825792,-52052557824,125341483008,-200310358016,212355661824,-240919445504,542252351488,-1009901862912,931842899968,-243112411136,-96101892096]),(⟨0,3,2⟩,[0,32768,-1802240,37519360,-409567232,2665611264,-10960633856,28753985536,-45902135296,38548570112,-16252895232,39524401152,-93837295616,57620889600,21201223680,1560674304]),(⟨0,3,3⟩,[65536,-2097152,28442624,-207880192,823721984,-1125384192,-4992663552,29592387584,-66759491584,68270161920,-25726943232,67310977024,-212398309376,181906702336,1935015936]),(⟨0,3,4⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨0,3,5⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨0,3,6⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨0,4,0⟩,[0,131072,-4145152,47710208,-191332352,-845086720,13679869952,-74487103488,232098037760,-446640160768,531629686784,-464742907904,703838060544,-1416097628160,1556488110080,-504156061696,-245507555328]),(⟨0,4,1⟩,[0,-131072,3440640,-38830080,253558784,-1069744128,2959966208,-4541743104,-1675755520,28400943104,-66056126464,43333746688,96622411776,-188662874112,138313728,159052300288]),(⟨0,4,3⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨0,4,4⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨0,5,0⟩,[0,32768,-2850816,68321280,-788922368,5242257408,-21586345984,56047206400,-88296914944,75780161536,-43715035136,102637207552,-209879957504,127140855808,55133044736,-22345580544]),(⟨0,5,3⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨0,6,0⟩,[0,0,-262144,12386304,-205389824,1737949184,-8605532160,26099187712,-47491842048,47415427072,-30221008896,64897482752,-141895794688,100758388736,17563779072]),(⟨0,6,3⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨1,0,0⟩,[0,65536,-2998272,61554688,-756957184,6261407744,-36961845248,160610533376,-520439087104,1256908750848,-2240663552000,2944997834752,-3124150321152,3734452994048,-5746615320576,7326380900352,-5271029858304,898457763840,977837113344,-236499959808]),(⟨1,0,1⟩,[-16384,589824,-9961472,109363200,-897400832,5790613504,-29367877632,114857132032,-338821103616,735673434112,-1144349540352,1281822834688,-1324620955648,2128279977984,-3704833753088,3888344088576,-1308069396480,-1168308420608,915939999744]),(⟨1,0,2⟩,[0,32768,-98304,-14974976,284377088,-2560278528,14057242624,-51241451520,128161497088,-222646222848,278045753344,-297997402112,378387415040,-519393263616,603881177088,-714498211840,881266376704,-601359761408]),(⟨1,0,3⟩,[16384,-557056,8634368,-86474752,655310848,-3905716224,17775575040,-59280687104,139451285504,-221625286656,231316209664,-205661569024,341160083456,-598791782400,507908538368,-29050699776,-155306360832]),(⟨1,0,4⟩,[0,-131072,3440640,-38830080,253558784,-1070268416,2985656320,-4983193600,1975386112,12618825728,-33198997504,36031463424,-16420372480,35077554176,-130048163840,135468777472]),(⟨1,1,0⟩,[-16384,589824,-10354688,125059072,-1172602880,8618459136,-48444702720,204187648000,-637044457472,1451181686784,-2375329480704,2831266529280,-3031069589504,4582222315520,-7773826482176,8680567259136,-4118162227200,-1233148657664,1640427651072]),(⟨1,1,1⟩,[0,294912,-8896512,118407168,-932659200,4879040512,-17707614208,43462934528,-58371227648,-29553311744,332683329536,-698884538368,480800555008,677949259776,-1377350467584,-329343221760,2820348002304,-2208867139584]),(⟨1,1,2⟩,[16384,-557056,8110080,-67600384,364101632,-1340506112,3386621952,-5370642432,2740731904,10882547712,-37875269632,76518883328,-118981181440,123835285504,21448835072,-345084035072,375835099136]),(⟨1,1,3⟩,[0,-131072,3440640,-38830080,253558784,-1070268416,2985656320,-4983193600,1975386112,12618825728,-33198997504,36031463424,-16420372480,35077554176,-130048163840,135468777472]),(⟨1,2,0⟩,[0,32768,688128,-41156608,661291008,-5667389440,30405853184,-109082050560,269468467200,-466591842304,595363069952,-662762946560,769878360064,-723809501184,269398671360,-14643363840,554159800320,-722560090112]),(⟨1,2,1⟩,[16384,-557056,8110080,-67600384,364101632,-1338408960,3321348096,-4554850304,-2472525824,28523790336,-64134234112,61595549696,6022184960,-69515837440,110272397312,-292573446144,343735304192]),(⟨1,3,0⟩,[16384,-557056,8830976,-96534528,846217216,-5833785344,29677502464,-106971332608,265608282112,-439491330048,480811040768,-481681145856,893810950144,-1628432596992,1527588339712,-355076341760,-263445676032]),(⟨1,3,1⟩,[0,-131072,3440640,-38830080,253558784,-1069744128,2959966208,-4541743104,-1675755520,28400943104,-66056126464,43333746688,96622411776,-188662874112,138313728,159052300288]),(⟨1,3,3⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨1,3,4⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨1,4,0⟩,[0,-131072,3440640,-38830080,253558784,-1069744128,2959966208,-4541743104,-1675755520,28400943104,-66056126464,43333746688,96622411776,-188662874112,138313728,159052300288]),(⟨1,4,3⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨2,0,0⟩,[0,-131072,4734976,-73433088,639434752,-3373187072,10243080192,-9530900480,-60735619072,316953640960,-771476389888,1127029506048,-1134822096896,1436044935168,-2917049892864,4315827470336,-3042713927680,145410048000,690701942784]),(⟨2,0,1⟩,[0,98304,-2179072,13287424,66027520,-1480065024,10419683328,-42936844288,118263939072,-235379359744,371874217984,-510220943360,566439608320,-332200673280,-95646695424,10170875904,680805629952,-707690332160]),(⟨2,0,2⟩,[0,131072,-4866048,76644352,-673710080,3657629696,-12759646208,28433743872,-37760892928,24711528448,-12947537920,57824411648,-129659371520,90770964480,84529299456,-227654533120,179774586880]),(⟨2,0,3⟩,[0,0,-1048576,30801920,-379355136,2576646144,-10625712128,27293220864,-42394779648,37231591424,-27462139904,63112806400,-116042661888,69519966208,33931821056,-23906254848]),(⟨2,1,0⟩,[0,32768,688128,-41156608,661291008,-5667389440,30405853184,-109082050560,269468467200,-466591842304,595363069952,-662762946560,769878360064,-723809501184,269398671360,-14643363840,554159800320,-722560090112]),(⟨2,1,1⟩,[16384,-557056,8110080,-67600384,364101632,-1338408960,3321348096,-4554850304,-2472525824,28523790336,-64134234112,61595549696,6022184960,-69515837440,110272397312,-292573446144,343735304192]),(⟨2,2,0⟩,[0,262144,-9732096,153288704,-1347682304,7322599424,-25602654208,57371852800,-77299908608,52759625728,-25527025664,94939447296,-205027409920,129493762048,114415730688,-241310433280,177650335744]),(⟨2,3,0⟩,[0,32768,-2850816,68321280,-788922368,5242257408,-21586345984,56047206400,-88296914944,75780161536,-43715035136,102637207552,-209879957504,127140855808,55133044736,-22345580544]),(⟨2,3,2⟩,[0,262144,-9895936,156041216,-1344733184,6906511360,-21126578176,32814792704,5505679360,-132662820864,261732237312,-217463586816,25423577088,56174641152]),(⟨2,3,3⟩,[-131072,3801088,-44236800,265682944,-861077504,1207173120,1257373696,-8286109696,14278983680,-10100801536,-10317922304,46169718784,-46457356288]),(⟨2,4,2⟩,[0,-524288,16318464,-203948032,1303314432,-4410310656,6564741120,3730833408,-31250841600,48337780736,-22205890560,-13127647232,8024948736]),(⟨2,5,2⟩,[0,-131072,6422528,-110362624,912785408,-3945529344,8214282240,-1825570816,-28260696064,55935107072,-32546619392,-5895880704]),(⟨2,5,5⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨3,0,0⟩,[0,-98304,5521408,-122437632,1490927616,-11394498560,58435878912,-207602827264,514109030400,-873060745216,996507631616,-890020151296,1237341585408,-2282660937728,2543737061376,-1005536034816,-328898265088,113450631168]),(⟨3,0,1⟩,[16384,-557056,8306688,-77660160,554483712,-3253895168,15121825792,-52052557824,125341483008,-200310358016,212355661824,-240919445504,542252351488,-1009901862912,931842899968,-243112411136,-96101892096]),(⟨3,0,2⟩,[0,32768,-1802240,37519360,-409567232,2665611264,-10960633856,28753985536,-45902135296,38548570112,-16252895232,39524401152,-93837295616,57620889600,21201223680,1560674304]),(⟨3,0,3⟩,[65536,-2097152,28442624,-207880192,823721984,-1125384192,-4992663552,29592387584,-66759491584,68270161920,-25726943232,67310977024,-212398309376,181906702336,1935015936]),(⟨3,0,4⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨3,0,5⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨3,0,6⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨3,1,0⟩,[16384,-557056,8830976,-96534528,846217216,-5833785344,29677502464,-106971332608,265608282112,-439491330048,480811040768,-481681145856,893810950144,-1628432596992,1527588339712,-355076341760,-263445676032]),(⟨3,1,1⟩,[0,-131072,3440640,-38830080,253558784,-1069744128,2959966208,-4541743104,-1675755520,28400943104,-66056126464,43333746688,96622411776,-188662874112,138313728,159052300288]),(⟨3,1,3⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨3,1,4⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨3,2,0⟩,[0,32768,-2850816,68321280,-788922368,5242257408,-21586345984,56047206400,-88296914944,75780161536,-43715035136,102637207552,-209879957504,127140855808,55133044736,-22345580544]),(⟨3,2,2⟩,[0,262144,-9895936,156041216,-1344733184,6906511360,-21126578176,32814792704,5505679360,-132662820864,261732237312,-217463586816,25423577088,56174641152]),(⟨3,2,3⟩,[-131072,3801088,-44236800,265682944,-861077504,1207173120,1257373696,-8286109696,14278983680,-10100801536,-10317922304,46169718784,-46457356288]),(⟨3,3,0⟩,[65536,-2097152,28180480,-195493888,618332160,612564992,-13598195712,55691575296,-114251333632,115685588992,-55947952128,132208459776,-354294104064,282665091072,19498795008]),(⟨3,3,1⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨3,3,2⟩,[-131072,3801088,-44236800,265682944,-861077504,1207173120,1257373696,-8286109696,14278983680,-10100801536,-10317922304,46169718784,-46457356288]),(⟨3,3,3⟩,[0,1572864,-34996224,297664512,-1178075136,1715994624,2290876416,-9497739264,2842165248,10962862080,12890800128,-33176027136]),(⟨3,4,0⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨3,4,1⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨3,5,0⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨3,6,0⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨4,0,0⟩,[0,131072,-4145152,47710208,-191332352,-845086720,13679869952,-74487103488,232098037760,-446640160768,531629686784,-464742907904,703838060544,-1416097628160,1556488110080,-504156061696,-245507555328]),(⟨4,0,1⟩,[0,-131072,3440640,-38830080,253558784,-1069744128,2959966208,-4541743104,-1675755520,28400943104,-66056126464,43333746688,96622411776,-188662874112,138313728,159052300288]),(⟨4,0,3⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨4,0,4⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨4,1,0⟩,[0,-131072,3440640,-38830080,253558784,-1069744128,2959966208,-4541743104,-1675755520,28400943104,-66056126464,43333746688,96622411776,-188662874112,138313728,159052300288]),(⟨4,1,3⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨4,2,2⟩,[0,-524288,16318464,-203948032,1303314432,-4410310656,6564741120,3730833408,-31250841600,48337780736,-22205890560,-13127647232,8024948736]),(⟨4,3,0⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨4,3,1⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨4,4,0⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨5,0,0⟩,[0,32768,-2850816,68321280,-788922368,5242257408,-21586345984,56047206400,-88296914944,75780161536,-43715035136,102637207552,-209879957504,127140855808,55133044736,-22345580544]),(⟨5,0,3⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨5,2,2⟩,[0,-131072,6422528,-110362624,912785408,-3945529344,8214282240,-1825570816,-28260696064,55935107072,-32546619392,-5895880704]),(⟨5,2,5⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨5,3,0⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨5,5,2⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨6,0,0⟩,[0,0,-262144,12386304,-205389824,1737949184,-8605532160,26099187712,-47491842048,47415427072,-30221008896,64897482752,-141895794688,100758388736,17563779072]),(⟨6,0,3⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨6,3,0⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,0⟩,[0,-512,11584,-106560,532736,-1621824,3051904,-3282624,1363712,606272,-407232]),(⟨0,0,1⟩,[0,-256,6592,-65600,337472,-994752,1716288,-1563072,348096,460992]),(⟨0,0,2⟩,[0,512,-9792,66304,-201792,309760,-192192,-87808,65856]),(⟨0,0,3⟩,[0,128,-4736,47104,-188672,361600,-281728,-48384])]

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,131072,-5586944,108609536,-1282539520,10320969728,-60028764160,260349067264,-853953052672,2121850978304,-3966701420544,5565447471104,-6213500665856,7080567275520,-10232679612416,13760482934784,-11757591166976,3980275056640,1507321413632,-1332591476736,208919789568]),(⟨0,0,1⟩,[0,65536,-3784704,90488832,-1234698240,10968760320,-67948806144,304750329856,-1007559245824,2464568573952,-4435978092544,5910021963776,-6483436109824,8186766426112,-12922263142400,16554558029824,-12042928521216,2141097492480,2471187955712,-876499255296]),(⟨0,0,2⟩,[0,-262144,10059776,-168640512,1634549760,-10177822720,42419666944,-117354151936,195458711552,-104631517184,-312020320256,781744357376,-774591102976,770512011264,-2159609626624,4078234976256,-3249022320640,227811999744,703837618176]),(⟨0,0,3⟩,[0,-98304,6569984,-156909568,1990344704,-15627010048,81840455680,-296300855296,748181274624,-1299848249344,1527105634304,-1391830548480,1862160924672,-3358378278912,3765472247808,-1497068519424,-561698521088,261279105024]),(⟨0,0,4⟩,[0,131072,-4145152,47710208,-191332352,-845086720,13679869952,-74487103488,232098037760,-446640160768,531629686784,-464742907904,703838060544,-1416097628160,1556488110080,-504156061696,-245507555328]),(⟨0,0,5⟩,[0,32768,-2850816,68321280,-788922368,5242257408,-21586345984,56047206400,-88296914944,75780161536,-43715035136,102637207552,-209879957504,127140855808,55133044736,-22345580544]),(⟨0,0,6⟩,[0,0,-262144,12386304,-205389824,1737949184,-8605532160,26099187712,-47491842048,47415427072,-30221008896,64897482752,-141895794688,100758388736,17563779072]),(⟨0,1,0⟩,[0,65536,-3784704,90488832,-1234698240,10968760320,-67948806144,304750329856,-1007559245824,2464568573952,-4435978092544,5910021963776,-6483436109824,8186766426112,-12922263142400,16554558029824,-12042928521216,2141097492480,2471187955712,-876499255296]),(⟨0,1,1⟩,[-16384,589824,-10354688,125059072,-1172602880,8616361984,-48372088832,203118886912,-628276789248,1407217254400,-2239009619968,2599019003904,-2987934318592,5354845093888,-9609334915072,10576199467008,-4743510409216,-1588708982784,1838922301440]),(⟨0,1,2⟩,[0,32768,688128,-41156608,661291008,-5667389440,30405853184,-109082050560,269468467200,-466591842304,595363069952,-662762946560,769878360064,-723809501184,269398671360,-14643363840,554159800320,-722560090112]),(⟨0,1,3⟩,[16384,-557056,8830976,-96534528,846217216,-5833785344,29677502464,-106971332608,265608282112,-439491330048,480811040768,-481681145856,893810950144,-1628432596992,1527588339712,-355076341760,-263445676032]),(⟨0,1,4⟩,[0,-131072,3440640,-38830080,253558784,-1069744128,2959966208,-4541743104,-1675755520,28400943104,-66056126464,43333746688,96622411776,-188662874112,138313728,159052300288]),(⟨0,2,0⟩,[0,-262144,10059776,-168640512,1634549760,-10177822720,42419666944,-117354151936,195458711552,-104631517184,-312020320256,781744357376,-774591102976,770512011264,-2159609626624,4078234976256,-3249022320640,227811999744,703837618176]),(⟨0,2,1⟩,[0,32768,688128,-41156608,661291008,-5667389440,30405853184,-109082050560,269468467200,-466591842304,595363069952,-662762946560,769878360064,-723809501184,269398671360,-14643363840,554159800320,-722560090112]),(⟨0,2,2⟩,[0,262144,-9732096,153288704,-1347682304,7322599424,-25602654208,57371852800,-77299908608,52759625728,-25527025664,94939447296,-205027409920,129493762048,114415730688,-241310433280,177650335744]),(⟨0,2,3⟩,[0,32768,-2850816,68321280,-788922368,5242257408,-21586345984,56047206400,-88296914944,75780161536,-43715035136,102637207552,-209879957504,127140855808,55133044736,-22345580544]),(⟨0,3,0⟩,[0,-98304,6569984,-156909568,1990344704,-15627010048,81840455680,-296300855296,748181274624,-1299848249344,1527105634304,-1391830548480,1862160924672,-3358378278912,3765472247808,-1497068519424,-561698521088,261279105024]),(⟨0,3,1⟩,[16384,-557056,8830976,-96534528,846217216,-5833785344,29677502464,-106971332608,265608282112,-439491330048,480811040768,-481681145856,893810950144,-1628432596992,1527588339712,-355076341760,-263445676032]),(⟨0,3,2⟩,[0,32768,-2850816,68321280,-788922368,5242257408,-21586345984,56047206400,-88296914944,75780161536,-43715035136,102637207552,-209879957504,127140855808,55133044736,-22345580544]),(⟨0,3,3⟩,[65536,-2097152,28180480,-195493888,618332160,612564992,-13598195712,55691575296,-114251333632,115685588992,-55947952128,132208459776,-354294104064,282665091072,19498795008]),(⟨0,3,4⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨0,3,5⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨0,3,6⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨0,4,0⟩,[0,131072,-4145152,47710208,-191332352,-845086720,13679869952,-74487103488,232098037760,-446640160768,531629686784,-464742907904,703838060544,-1416097628160,1556488110080,-504156061696,-245507555328]),(⟨0,4,1⟩,[0,-131072,3440640,-38830080,253558784,-1069744128,2959966208,-4541743104,-1675755520,28400943104,-66056126464,43333746688,96622411776,-188662874112,138313728,159052300288]),(⟨0,4,3⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨0,4,4⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨0,5,0⟩,[0,32768,-2850816,68321280,-788922368,5242257408,-21586345984,56047206400,-88296914944,75780161536,-43715035136,102637207552,-209879957504,127140855808,55133044736,-22345580544]),(⟨0,5,3⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨0,6,0⟩,[0,0,-262144,12386304,-205389824,1737949184,-8605532160,26099187712,-47491842048,47415427072,-30221008896,64897482752,-141895794688,100758388736,17563779072]),(⟨0,6,3⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨1,0,0⟩,[0,65536,-3784704,90488832,-1234698240,10968760320,-67948806144,304750329856,-1007559245824,2464568573952,-4435978092544,5910021963776,-6483436109824,8186766426112,-12922263142400,16554558029824,-12042928521216,2141097492480,2471187955712,-876499255296]),(⟨1,0,1⟩,[-16384,589824,-10354688,125059072,-1172602880,8616361984,-48372088832,203118886912,-628276789248,1407217254400,-2239009619968,2599019003904,-2987934318592,5354845093888,-9609334915072,10576199467008,-4743510409216,-1588708982784,1838922301440]),(⟨1,0,2⟩,[0,32768,688128,-41156608,661291008,-5667389440,30405853184,-109082050560,269468467200,-466591842304,595363069952,-662762946560,769878360064,-723809501184,269398671360,-14643363840,554159800320,-722560090112]),(⟨1,0,3⟩,[16384,-557056,8830976,-96534528,846217216,-5833785344,29677502464,-106971332608,265608282112,-439491330048,480811040768,-481681145856,893810950144,-1628432596992,1527588339712,-355076341760,-263445676032]),(⟨1,0,4⟩,[0,-131072,3440640,-38830080,253558784,-1069744128,2959966208,-4541743104,-1675755520,28400943104,-66056126464,43333746688,96622411776,-188662874112,138313728,159052300288]),(⟨1,1,0⟩,[-16384,589824,-10354688,125059072,-1172602880,8616361984,-48372088832,203118886912,-628276789248,1407217254400,-2239009619968,2599019003904,-2987934318592,5354845093888,-9609334915072,10576199467008,-4743510409216,-1588708982784,1838922301440]),(⟨1,1,1⟩,[0,294912,-8896512,118407168,-932659200,4877991936,-17668030464,42838769664,-52992294912,-57179357184,417189642240,-830143709184,458777837568,1208600543232,-2424279416832,540511125504,2718653693952,-2433565704192]),(⟨1,1,2⟩,[16384,-557056,8110080,-67600384,364101632,-1338408960,3321348096,-4554850304,-2472525824,28523790336,-64134234112,61595549696,6022184960,-69515837440,110272397312,-292573446144,343735304192]),(⟨1,1,3⟩,[0,-131072,3440640,-38830080,253558784,-1069744128,2959966208,-4541743104,-1675755520,28400943104,-66056126464,43333746688,96622411776,-188662874112,138313728,159052300288]),(⟨1,2,0⟩,[0,32768,688128,-41156608,661291008,-5667389440,30405853184,-109082050560,269468467200,-466591842304,595363069952,-662762946560,769878360064,-723809501184,269398671360,-14643363840,554159800320,-722560090112]),(⟨1,2,1⟩,[16384,-557056,8110080,-67600384,364101632,-1338408960,3321348096,-4554850304,-2472525824,28523790336,-64134234112,61595549696,6022184960,-69515837440,110272397312,-292573446144,343735304192]),(⟨1,3,0⟩,[16384,-557056,8830976,-96534528,846217216,-5833785344,29677502464,-106971332608,265608282112,-439491330048,480811040768,-481681145856,893810950144,-1628432596992,1527588339712,-355076341760,-263445676032]),(⟨1,3,1⟩,[0,-131072,3440640,-38830080,253558784,-1069744128,2959966208,-4541743104,-1675755520,28400943104,-66056126464,43333746688,96622411776,-188662874112,138313728,159052300288]),(⟨1,3,3⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨1,3,4⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨1,4,0⟩,[0,-131072,3440640,-38830080,253558784,-1069744128,2959966208,-4541743104,-1675755520,28400943104,-66056126464,43333746688,96622411776,-188662874112,138313728,159052300288]),(⟨1,4,3⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨2,0,0⟩,[0,-262144,10059776,-168640512,1634549760,-10177822720,42419666944,-117354151936,195458711552,-104631517184,-312020320256,781744357376,-774591102976,770512011264,-2159609626624,4078234976256,-3249022320640,227811999744,703837618176]),(⟨2,0,1⟩,[0,32768,688128,-41156608,661291008,-5667389440,30405853184,-109082050560,269468467200,-466591842304,595363069952,-662762946560,769878360064,-723809501184,269398671360,-14643363840,554159800320,-722560090112]),(⟨2,0,2⟩,[0,262144,-9732096,153288704,-1347682304,7322599424,-25602654208,57371852800,-77299908608,52759625728,-25527025664,94939447296,-205027409920,129493762048,114415730688,-241310433280,177650335744]),(⟨2,0,3⟩,[0,32768,-2850816,68321280,-788922368,5242257408,-21586345984,56047206400,-88296914944,75780161536,-43715035136,102637207552,-209879957504,127140855808,55133044736,-22345580544]),(⟨2,1,0⟩,[0,32768,688128,-41156608,661291008,-5667389440,30405853184,-109082050560,269468467200,-466591842304,595363069952,-662762946560,769878360064,-723809501184,269398671360,-14643363840,554159800320,-722560090112]),(⟨2,1,1⟩,[16384,-557056,8110080,-67600384,364101632,-1338408960,3321348096,-4554850304,-2472525824,28523790336,-64134234112,61595549696,6022184960,-69515837440,110272397312,-292573446144,343735304192]),(⟨2,2,0⟩,[0,262144,-9732096,153288704,-1347682304,7322599424,-25602654208,57371852800,-77299908608,52759625728,-25527025664,94939447296,-205027409920,129493762048,114415730688,-241310433280,177650335744]),(⟨2,2,2⟩,[0,524288,-18153472,267190272,-2191917056,10991108096,-34079965184,58061881344,-10783817728,-193155694592,458877108224,-473908051968,156337045504,88890081280,-49623662592]),(⟨2,2,3⟩,[0,262144,-9895936,156041216,-1344733184,6906511360,-21126578176,32814792704,5505679360,-132662820864,261732237312,-217463586816,25423577088,56174641152]),(⟨2,2,4⟩,[0,-524288,16318464,-203948032,1303314432,-4410310656,6564741120,3730833408,-31250841600,48337780736,-22205890560,-13127647232,8024948736]),(⟨2,2,5⟩,[0,-131072,6422528,-110362624,912785408,-3945529344,8214282240,-1825570816,-28260696064,55935107072,-32546619392,-5895880704]),(⟨2,3,0⟩,[0,32768,-2850816,68321280,-788922368,5242257408,-21586345984,56047206400,-88296914944,75780161536,-43715035136,102637207552,-209879957504,127140855808,55133044736,-22345580544]),(⟨2,3,2⟩,[0,262144,-9895936,156041216,-1344733184,6906511360,-21126578176,32814792704,5505679360,-132662820864,261732237312,-217463586816,25423577088,56174641152]),(⟨2,3,3⟩,[-131072,3801088,-44236800,265682944,-861077504,1207173120,1257373696,-8286109696,14278983680,-10100801536,-10317922304,46169718784,-46457356288]),(⟨2,4,2⟩,[0,-524288,16318464,-203948032,1303314432,-4410310656,6564741120,3730833408,-31250841600,48337780736,-22205890560,-13127647232,8024948736]),(⟨2,5,2⟩,[0,-131072,6422528,-110362624,912785408,-3945529344,8214282240,-1825570816,-28260696064,55935107072,-32546619392,-5895880704]),(⟨2,5,5⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨3,0,0⟩,[0,-98304,6569984,-156909568,1990344704,-15627010048,81840455680,-296300855296,748181274624,-1299848249344,1527105634304,-1391830548480,1862160924672,-3358378278912,3765472247808,-1497068519424,-561698521088,261279105024]),(⟨3,0,1⟩,[16384,-557056,8830976,-96534528,846217216,-5833785344,29677502464,-106971332608,265608282112,-439491330048,480811040768,-481681145856,893810950144,-1628432596992,1527588339712,-355076341760,-263445676032]),(⟨3,0,2⟩,[0,32768,-2850816,68321280,-788922368,5242257408,-21586345984,56047206400,-88296914944,75780161536,-43715035136,102637207552,-209879957504,127140855808,55133044736,-22345580544]),(⟨3,0,3⟩,[65536,-2097152,28180480,-195493888,618332160,612564992,-13598195712,55691575296,-114251333632,115685588992,-55947952128,132208459776,-354294104064,282665091072,19498795008]),(⟨3,0,4⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨3,0,5⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨3,0,6⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨3,1,0⟩,[16384,-557056,8830976,-96534528,846217216,-5833785344,29677502464,-106971332608,265608282112,-439491330048,480811040768,-481681145856,893810950144,-1628432596992,1527588339712,-355076341760,-263445676032]),(⟨3,1,1⟩,[0,-131072,3440640,-38830080,253558784,-1069744128,2959966208,-4541743104,-1675755520,28400943104,-66056126464,43333746688,96622411776,-188662874112,138313728,159052300288]),(⟨3,1,3⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨3,1,4⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨3,2,0⟩,[0,32768,-2850816,68321280,-788922368,5242257408,-21586345984,56047206400,-88296914944,75780161536,-43715035136,102637207552,-209879957504,127140855808,55133044736,-22345580544]),(⟨3,2,2⟩,[0,262144,-9895936,156041216,-1344733184,6906511360,-21126578176,32814792704,5505679360,-132662820864,261732237312,-217463586816,25423577088,56174641152]),(⟨3,2,3⟩,[-131072,3801088,-44236800,265682944,-861077504,1207173120,1257373696,-8286109696,14278983680,-10100801536,-10317922304,46169718784,-46457356288]),(⟨3,3,0⟩,[65536,-2097152,28180480,-195493888,618332160,612564992,-13598195712,55691575296,-114251333632,115685588992,-55947952128,132208459776,-354294104064,282665091072,19498795008]),(⟨3,3,1⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨3,3,2⟩,[-131072,3801088,-44236800,265682944,-861077504,1207173120,1257373696,-8286109696,14278983680,-10100801536,-10317922304,46169718784,-46457356288]),(⟨3,3,3⟩,[0,1572864,-34996224,297664512,-1178075136,1715994624,2290876416,-9497739264,2842165248,10962862080,12890800128,-33176027136]),(⟨3,4,0⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨3,4,1⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨3,5,0⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨3,6,0⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨4,0,0⟩,[0,131072,-4145152,47710208,-191332352,-845086720,13679869952,-74487103488,232098037760,-446640160768,531629686784,-464742907904,703838060544,-1416097628160,1556488110080,-504156061696,-245507555328]),(⟨4,0,1⟩,[0,-131072,3440640,-38830080,253558784,-1069744128,2959966208,-4541743104,-1675755520,28400943104,-66056126464,43333746688,96622411776,-188662874112,138313728,159052300288]),(⟨4,0,3⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨4,0,4⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨4,1,0⟩,[0,-131072,3440640,-38830080,253558784,-1069744128,2959966208,-4541743104,-1675755520,28400943104,-66056126464,43333746688,96622411776,-188662874112,138313728,159052300288]),(⟨4,1,3⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨4,2,2⟩,[0,-524288,16318464,-203948032,1303314432,-4410310656,6564741120,3730833408,-31250841600,48337780736,-22205890560,-13127647232,8024948736]),(⟨4,3,0⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨4,3,1⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨4,4,0⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨5,0,0⟩,[0,32768,-2850816,68321280,-788922368,5242257408,-21586345984,56047206400,-88296914944,75780161536,-43715035136,102637207552,-209879957504,127140855808,55133044736,-22345580544]),(⟨5,0,3⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨5,2,2⟩,[0,-131072,6422528,-110362624,912785408,-3945529344,8214282240,-1825570816,-28260696064,55935107072,-32546619392,-5895880704]),(⟨5,2,5⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨5,3,0⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨5,5,2⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨6,0,0⟩,[0,0,-262144,12386304,-205389824,1737949184,-8605532160,26099187712,-47491842048,47415427072,-30221008896,64897482752,-141895794688,100758388736,17563779072]),(⟨6,0,3⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨6,3,0⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712])]


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
    (Poly.add (Poly.scale (K.ofRat r724) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 9 13).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r723*r723 : ℚ)=r724 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 9 13 r723 r723 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 9=13 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 9 13).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C139

#print axioms Coulomb8.Columns.C139.sound
