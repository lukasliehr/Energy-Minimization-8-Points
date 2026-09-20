import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C128

def r0 : ℚ := { num := -65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 360448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -43548672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 445743104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -2994798592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 13605732352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -39936950272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 54996926464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 107463376896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -831490162688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 2434323808256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -4441765150720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 5595609497600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -5893343477760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 8020896219136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -1879506518016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 15840988626944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -10737996759040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 3181760806912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -46623621120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 1802240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -39387136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 475561984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -513769472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 1049067520, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -56507105280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 90333937664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 94111563776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -986641694720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 2924469026816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -5143570841600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 6086867451904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -6401801945088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 10080700989440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -17489153261568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 2823552106496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -1608304033792, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 38462095360, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -4423680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 62652416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -480706560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 121831424, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -3813539840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -8556576768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 74967023616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -214368780288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 5740953600, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 28116385792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -95273943040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 880418160640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -450493677568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 1178306412544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -4190687985664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 335851028480, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -386623700992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -3571712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 71172096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -735805440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 4441309184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -15663529984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 24576786432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 42646667264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := -340940750848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := 130374926336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := -81219682304, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := 1284256661504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -1211423064064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 2477569900544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -84480622592, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 3105710243840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := -62500241408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := 1638400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := -11567104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -32407552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 926613504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -5692719104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 924549120, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -7449968640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := -12645367808, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := 307708624896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := -491210244096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 60601761792, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -389110497280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := 1032277590016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := -37091377152, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := 24448434176, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 1769472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := -31391744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 262012928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -1101561856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 1708589056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := 4591124480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -29146480640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 65647575040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -75218485248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 42168680448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := -46515486720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := 165462310912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -199185596416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 836960256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -7929856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := 89194496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -477691904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 1089798144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 958267392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -256770048, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 33560068096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -41867149312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 22426615808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -25757417472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 107051417600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := -18818334720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := 524288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := -19070976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := 297402368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := -2637692928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := 14646968320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := -51364823040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 99287302144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -1154088960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -602656407552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 1870005469184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -3030031663104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 3063501553664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := -3530564239360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 8233728409600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -15255002415104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 2129422581760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -121433030656, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -1736704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 33456128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -327024640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 1790869504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := -5162303488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := 2515959808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 39009386496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -162985574400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 336940007424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -420447551488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 409661734912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -596862599168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 853281636352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := -132892622848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -12302680064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 30419976192, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -589824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 19628032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -265256960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 273678336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := -160890880, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 2314764288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := 93749248, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -2573467648, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 362042687488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -74523246592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 420622467072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := -476953968640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := 1334392848384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := -297145630720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := 24617123840, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 1048576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -25427968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 251920384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := -1328807936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 558628864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := -5318901760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -2394423296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := 17447780352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := -8840019968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -32790282240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -24424218624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 40917794816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := -398196736, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 4194304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -54001664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := 354549760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := -1179779072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := 996278272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 7297564672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := -32630636544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 66045214720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -73597190144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 37111726080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -1614675968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 42852810752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -126366384128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 26986676224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -4178837504, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -327680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := -2686976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := 851968, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := -72450048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -1154744320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 8203993088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -25653280768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := 2728230912, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := -54363750400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := 46662746112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := -44101992448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := 94959796224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -118037282816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -1395720192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := -393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := 10289152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -15663104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := 86966272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -1792212992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 2014969856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := 3122528256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -11618615296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 7292583936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := 8775073792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 7330267136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -7845773312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := 57475072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 1966080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := -196608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := 139591680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := -59506688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := 373030912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 68550656, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -3108765696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 706150400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := 415891456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := 3342794752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := -1047134208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := -1179648, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -11665408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := 99221504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -56098816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 571998208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := 763625472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -3165913088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 947388416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := 214958080, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := 4296933376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := -92930048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := 4718592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -40894464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := 262144000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := -1404829696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := 5946474496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := -18918408192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 43882905600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -69149130752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 62403379200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := -5264900096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 104262008832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -23957602304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := -417595392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := 8126464, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := 7995392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -2429288448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 131137536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -2348417024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := 9470672896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := 236322816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := -19005440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -2359296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := 66453504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := -796262400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 763625472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := -21895839744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := 53727068160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := -61070770176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -43160961024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 1688469504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := -1887830016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := -608455753728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := -10290462720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := 541996351488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := -145843421184, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := 5441716224, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := -55574528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := 399245312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := -1695940608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := 4216586240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := -5086380032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := -709361664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := 9601941504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := -14677442560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := 2940731392, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := -26669219840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := 269165658112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 15667560448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -487325696, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := -1048576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := 25165824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := -12582912, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := 679477248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := 211812352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := -5259657216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := 6127878144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := 75497472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := -2097152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := 50331648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := -25165824, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := 1358954496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := 423624704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := -10519314432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := 12255756288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 150994944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := 7995392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := -99221504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := 634257408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := -2049048576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := 1311768576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 15376056320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -62926356480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 101224808448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := -104202240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := -301741506560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := 548445487104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := -57164038144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := 93061120, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := 8519680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := -110755840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := 732299264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := -2470313984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := 2463367168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 11780489216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := -49630412800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 72531050496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := 455737344, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := -204964233216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := 48681320448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := -254672896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -6815744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 64749568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -248250368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 46661632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := 20971520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := -434634752, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := 6863454208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := 9763553280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := -38675152896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := 5785255936, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := -7077888, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -4194304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := 48365568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := -33554432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := 14942208, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := 1950351360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := -7990935552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := 10007609344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := 9069789184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := -6501171200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := 53084160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := 1572864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := -36962304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := 19660800, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := -1427111936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := 50331648, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := 1990721536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := -15396765696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := 447741952, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := 2269642752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := -37699715072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := 250871808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -6291456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := 3145728, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := -169869312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := -52953088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := 1314914304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := -1531969536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := -18874368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := 180224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := -21774336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := 222871552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := -1497399296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := 6802866176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := -19968475136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := 27498463232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := 53731688448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := -415745081344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := 1217161904128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := -2220882575360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := 2797804748800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := -2946671738880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := 4010448109568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := -939753259008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := 7920494313472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := -5368998379520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := 1590880403456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := -23311810560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := -16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 901120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := -19693568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := 237780992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := -256884736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := 524533760, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := -28253552640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := 45166968832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := 47055781888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := -493320847360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := 1462234513408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := -2571785420800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := 3043433725952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := -3200900972544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := 5040350494720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := -8744576630784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := 1411776053248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := -804152016896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := 19231047680, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := -2211840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := 31326208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := -240353280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := 60915712, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := -1906769920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := -4278288384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := 37483511808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := -107184390144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := 2870476800, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := 14058192896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := -47636971520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := 440209080320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := -225246838784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := 589153206272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := -2095343992832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := 167925514240, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := -193311850496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := -1785856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := 35586048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := -367902720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := 2220654592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := -7831764992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := 12288393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := 21323333632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := -170470375424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := 65187463168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := -40609841152, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := 642128330752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := -605711532032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := 1238784950272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := -42240311296, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := 1552855121920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := -31250120704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := 819200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := -5783552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := -16203776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := 463306752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := -2846359552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := 462274560, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := -3724984320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := -6322683904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := 153854312448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := -245605122048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r454 : ℚ := { num := 30300880896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r455 : ℚ := { num := -194555248640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r456 : ℚ := { num := 516138795008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r457 : ℚ := { num := -18545688576, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r458 : ℚ := { num := 12224217088, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r459 : ℚ := { num := 884736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r460 : ℚ := { num := -15695872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r461 : ℚ := { num := 131006464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r462 : ℚ := { num := -550780928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r463 : ℚ := { num := 854294528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r464 : ℚ := { num := 2295562240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r465 : ℚ := { num := -14573240320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r466 : ℚ := { num := 32823787520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r467 : ℚ := { num := -37609242624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r468 : ℚ := { num := 21084340224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r469 : ℚ := { num := -23257743360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r470 : ℚ := { num := 82731155456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r471 : ℚ := { num := -99592798208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r472 : ℚ := { num := 418480128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r473 : ℚ := { num := -3964928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r474 : ℚ := { num := 44597248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r475 : ℚ := { num := -238845952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r476 : ℚ := { num := 544899072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r477 : ℚ := { num := 479133696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r478 : ℚ := { num := -128385024, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r479 : ℚ := { num := 16780034048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r480 : ℚ := { num := -20933574656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r481 : ℚ := { num := 11213307904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r482 : ℚ := { num := -12878708736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r483 : ℚ := { num := 53525708800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r484 : ℚ := { num := -9409167360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r485 : ℚ := { num := -9535488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r486 : ℚ := { num := 148701184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r487 : ℚ := { num := -1318846464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r488 : ℚ := { num := 7323484160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r489 : ℚ := { num := -25682411520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r490 : ℚ := { num := 49643651072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r491 : ℚ := { num := -577044480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r492 : ℚ := { num := -301328203776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r493 : ℚ := { num := 935002734592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r494 : ℚ := { num := -1515015831552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r495 : ℚ := { num := 1531750776832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r496 : ℚ := { num := -1765282119680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r497 : ℚ := { num := 4116864204800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r498 : ℚ := { num := -7627501207552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r499 : ℚ := { num := 1064711290880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r500 : ℚ := { num := -60716515328, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r501 : ℚ := { num := 16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r502 : ℚ := { num := -868352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r503 : ℚ := { num := 16728064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r504 : ℚ := { num := -163512320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r505 : ℚ := { num := 895434752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r506 : ℚ := { num := -2581151744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r507 : ℚ := { num := 1257979904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r508 : ℚ := { num := 19504693248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r509 : ℚ := { num := -81492787200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r510 : ℚ := { num := 168470003712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r511 : ℚ := { num := -210223775744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r512 : ℚ := { num := 204830867456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r513 : ℚ := { num := -298431299584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r514 : ℚ := { num := 426640818176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r515 : ℚ := { num := -66446311424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r516 : ℚ := { num := -6151340032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r517 : ℚ := { num := 15209988096, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r518 : ℚ := { num := -294912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r519 : ℚ := { num := 9814016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r520 : ℚ := { num := -132628480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r521 : ℚ := { num := 136839168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r522 : ℚ := { num := -80445440, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r523 : ℚ := { num := 1157382144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r524 : ℚ := { num := 46874624, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r525 : ℚ := { num := -1286733824, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r526 : ℚ := { num := 181021343744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r527 : ℚ := { num := -37261623296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r528 : ℚ := { num := 210311233536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r529 : ℚ := { num := -238476984320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r530 : ℚ := { num := 667196424192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r531 : ℚ := { num := -148572815360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r532 : ℚ := { num := 12308561920, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r533 : ℚ := { num := -12713984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r534 : ℚ := { num := 125960192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r535 : ℚ := { num := -664403968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r536 : ℚ := { num := 279314432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r537 : ℚ := { num := -2659450880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r538 : ℚ := { num := -1197211648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r539 : ℚ := { num := 8723890176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r540 : ℚ := { num := -4420009984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r541 : ℚ := { num := -16395141120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r542 : ℚ := { num := -12212109312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r543 : ℚ := { num := 20458897408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r544 : ℚ := { num := -199098368, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r545 : ℚ := { num := 2097152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r546 : ℚ := { num := -27000832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r547 : ℚ := { num := 177274880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r548 : ℚ := { num := -589889536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r549 : ℚ := { num := 498139136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r550 : ℚ := { num := 3648782336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r551 : ℚ := { num := -16315318272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r552 : ℚ := { num := 33022607360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r553 : ℚ := { num := -36798595072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r554 : ℚ := { num := 18555863040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r555 : ℚ := { num := -807337984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r556 : ℚ := { num := 21426405376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r557 : ℚ := { num := -63183192064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r558 : ℚ := { num := 13493338112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r559 : ℚ := { num := -2089418752, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r560 : ℚ := { num := -163840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r561 : ℚ := { num := -1343488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r562 : ℚ := { num := 425984, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r563 : ℚ := { num := -36225024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r564 : ℚ := { num := -577372160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r565 : ℚ := { num := 4101996544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r566 : ℚ := { num := -12826640384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r567 : ℚ := { num := 1364115456, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r568 : ℚ := { num := -27181875200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r569 : ℚ := { num := 23331373056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r570 : ℚ := { num := -22050996224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r571 : ℚ := { num := 47479898112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r572 : ℚ := { num := -59018641408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r573 : ℚ := { num := -697860096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r574 : ℚ := { num := -196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r575 : ℚ := { num := 5144576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r576 : ℚ := { num := -7831552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r577 : ℚ := { num := 43483136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r578 : ℚ := { num := -896106496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r579 : ℚ := { num := 1007484928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r580 : ℚ := { num := 1561264128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r581 : ℚ := { num := -5809307648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r582 : ℚ := { num := 3646291968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r583 : ℚ := { num := 4387536896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r584 : ℚ := { num := 3665133568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r585 : ℚ := { num := -3922886656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r586 : ℚ := { num := 28737536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r587 : ℚ := { num := 983040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r588 : ℚ := { num := -98304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r589 : ℚ := { num := 69795840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r590 : ℚ := { num := -29753344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r591 : ℚ := { num := 186515456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r592 : ℚ := { num := 34275328, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r593 : ℚ := { num := -1554382848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r594 : ℚ := { num := 353075200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r595 : ℚ := { num := 207945728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r596 : ℚ := { num := 1671397376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r597 : ℚ := { num := -523567104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r598 : ℚ := { num := -589824, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r599 : ℚ := { num := -5832704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r600 : ℚ := { num := 49610752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r601 : ℚ := { num := -28049408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r602 : ℚ := { num := 285999104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r603 : ℚ := { num := 381812736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r604 : ℚ := { num := -1582956544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r605 : ℚ := { num := 473694208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r606 : ℚ := { num := 107479040, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r607 : ℚ := { num := 2148466688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r608 : ℚ := { num := -46465024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r609 : ℚ := { num := 2359296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r610 : ℚ := { num := -20447232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r611 : ℚ := { num := 131072000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r612 : ℚ := { num := -702414848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r613 : ℚ := { num := 2973237248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r614 : ℚ := { num := -9459204096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r615 : ℚ := { num := 21941452800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r616 : ℚ := { num := -34574565376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r617 : ℚ := { num := 31201689600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r618 : ℚ := { num := -2632450048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r619 : ℚ := { num := 52131004416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r620 : ℚ := { num := -11978801152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r621 : ℚ := { num := -208797696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r622 : ℚ := { num := 4063232, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r623 : ℚ := { num := 3997696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r624 : ℚ := { num := -1214644224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r625 : ℚ := { num := 65568768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r626 : ℚ := { num := -1174208512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r627 : ℚ := { num := 4735336448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r628 : ℚ := { num := 118161408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r629 : ℚ := { num := -9502720, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r630 : ℚ := { num := -1179648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r631 : ℚ := { num := 33226752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r632 : ℚ := { num := -398131200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r633 : ℚ := { num := 381812736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r634 : ℚ := { num := -10947919872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r635 : ℚ := { num := 26863534080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r636 : ℚ := { num := -30535385088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r637 : ℚ := { num := -21580480512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r638 : ℚ := { num := 844234752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r639 : ℚ := { num := -943915008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r640 : ℚ := { num := -304227876864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r641 : ℚ := { num := -5145231360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r642 : ℚ := { num := 270998175744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r643 : ℚ := { num := -72921710592, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r644 : ℚ := { num := 2720858112, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r645 : ℚ := { num := -27787264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r646 : ℚ := { num := 199622656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r647 : ℚ := { num := -847970304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r648 : ℚ := { num := 2108293120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r649 : ℚ := { num := -2543190016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r650 : ℚ := { num := -354680832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r651 : ℚ := { num := 4800970752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r652 : ℚ := { num := -7338721280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r653 : ℚ := { num := 1470365696, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r654 : ℚ := { num := -13334609920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r655 : ℚ := { num := 134582829056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r656 : ℚ := { num := 7833780224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r657 : ℚ := { num := -243662848, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r658 : ℚ := { num := -524288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r659 : ℚ := { num := 12582912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r660 : ℚ := { num := -6291456, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r661 : ℚ := { num := 339738624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r662 : ℚ := { num := 105906176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r663 : ℚ := { num := -2629828608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r664 : ℚ := { num := 3063939072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r665 : ℚ := { num := 37748736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r666 : ℚ := { num := 3997696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r667 : ℚ := { num := -49610752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r668 : ℚ := { num := 317128704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r669 : ℚ := { num := -1024524288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r670 : ℚ := { num := 655884288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r671 : ℚ := { num := 7688028160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r672 : ℚ := { num := -31463178240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r673 : ℚ := { num := 50612404224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r674 : ℚ := { num := -52101120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r675 : ℚ := { num := -150870753280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r676 : ℚ := { num := 274222743552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r677 : ℚ := { num := -28582019072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r678 : ℚ := { num := 46530560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r679 : ℚ := { num := 4259840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r680 : ℚ := { num := -55377920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r681 : ℚ := { num := 366149632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r682 : ℚ := { num := -1235156992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r683 : ℚ := { num := 1231683584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r684 : ℚ := { num := 5890244608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r685 : ℚ := { num := -24815206400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r686 : ℚ := { num := 36265525248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r687 : ℚ := { num := 227868672, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r688 : ℚ := { num := -102482116608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r689 : ℚ := { num := 24340660224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r690 : ℚ := { num := -127336448, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r691 : ℚ := { num := -3407872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r692 : ℚ := { num := 32374784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r693 : ℚ := { num := -124125184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r694 : ℚ := { num := 23330816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r695 : ℚ := { num := 10485760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r696 : ℚ := { num := -217317376, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r697 : ℚ := { num := 3431727104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r698 : ℚ := { num := 4881776640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r699 : ℚ := { num := -19337576448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r700 : ℚ := { num := 2892627968, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r701 : ℚ := { num := -3538944, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r702 : ℚ := { num := 24182784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r703 : ℚ := { num := -16777216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r704 : ℚ := { num := 7471104, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r705 : ℚ := { num := 975175680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r706 : ℚ := { num := -3995467776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r707 : ℚ := { num := 5003804672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r708 : ℚ := { num := 4534894592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r709 : ℚ := { num := -3250585600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r710 : ℚ := { num := 26542080, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r711 : ℚ := { num := 786432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r712 : ℚ := { num := -18481152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r713 : ℚ := { num := 9830400, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r714 : ℚ := { num := -713555968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r715 : ℚ := { num := 25165824, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r716 : ℚ := { num := 995360768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r717 : ℚ := { num := -7698382848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r718 : ℚ := { num := 223870976, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r719 : ℚ := { num := 1134821376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r720 : ℚ := { num := -18849857536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r721 : ℚ := { num := 125435904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r722 : ℚ := { num := -3145728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r723 : ℚ := { num := 1572864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r724 : ℚ := { num := -84934656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r725 : ℚ := { num := -26476544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r726 : ℚ := { num := 657457152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r727 : ℚ := { num := -765984768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r728 : ℚ := { num := -9437184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r729 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r730 : ℚ := { num := 1, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19],[r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38],[r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56],[r57,r58,r59,r60,r61,r62,r63,r64,r65,r66,r67,r68,r69,r70,r71,r72,r73],[r0,r74,r75,r76,r77,r78,r79,r80,r81,r82,r83,r84,r85,r86,r87,r88],[r20,r89,r90,r91,r92,r93,r94,r95,r96,r97,r98,r99,r100,r101,r102],[0,r103,r104,r105,r106,r107,r108,r109,r110,r111,r112,r113,r114,r115],[],[],[],[],[],[],[0,r116,r117,r118,r119,r120,r121,r122,r123,r124,r125,r126,r127,r128,r129,r130,r131,r132],[r133,r134,r135,r136,r137,r138,r139,r140,r141,r142,r143,r144,r145,r146,r147,r148,r149],[0,r150,r151,r152,r153,r154,r155,r156,r157,r158,r159,r160,r161,r162,r163,r164],[0,0,r165,r166,r167,r168,r169,r170,r171,r172,r173,r174,r175,r176,r177],[],[],[],[],[],[],[],[r178,r179,r180,r181,r182,r183,r184,r185,r186,r187,r188,r189,r190,r191,r192,r193],[r133,r194,r195,r196,r197,r198,r199,r200,r201,r202,r203,r204,r205,r206,r207],[0,r208,r209,r210,r211,r212,r213,r214,r215,r216,r217,r218,r219,r220],[r0,r221,r222,r223,r224,r225,r226,r227,r228,r229,r230,r231,r232],[0,r116,r233,r234,r235,r236,r237,r238,r239,r240,r241,r242],[],[],[],[],[0,r243,r244,r245,r246,r247,r248,r249,r250,r251,r252,r253,r254,r255],[r0,r221,r222,r223,r256,r257,r258,r259,r260,r261,r262,r263,r264],[0,r116,r233,r234,r235,r236,r237,r238,r239,r240,r241,r242],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,0,r265,r266,r267,r268,r269,r270,r271,r272,r273,r274,r275,r276,r277,r278,r279],[0,r178,r179,r280,r281,r282,r283,r284,r285,r286,r287,r288,r289,r290,r291,r292],[0,0,r165,r166,r167,r168,r169,r170,r171,r172,r173,r174,r175,r176,r177],[],[],[],[],[],[],[],[],[0,r208,r209,r210,r211,r212,r213,r214,r215,r216,r217,r218,r219,r220],[0,0,0,0,r293,r294,r295,r296,r297,r298,r299,r300,-1048576],[],[],[],[],[],[0,0,0,0,r301,r302,r303,r304,r305,r306,r307,r308,-2097152],[],[],[],[],[],[],[],[],[],[],[],[r243,r309,r310,r311,r312,r313,r314,r315,r316,r317,r318,r319,r320,r321],[r243,r322,r323,r324,r325,r326,r327,r328,r329,r330,r331,r332,r333],[r103,r334,r335,r336,r337,r338,r339,r340,r341,r342,r343,r344],[r39,r345,r346,r347,r348,r349,r350,r351,r352,r353,r354],[],[],[],[0,r355,r356,r357,r358,r359,r360,r361,r362,r363,r364,r365],[],[],[],[],[],[r103,r366,r367,r368,r369,r370,r371,r372,262144],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[r20,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382,r383,r384,r385,r386,r387,r388,r389,r390,r391]),(⟨0,0,1⟩,[r392,r393,r394,r395,r396,r397,r398,r399,r400,r401,r402,r403,r404,r405,r406,r407,r408,r409,r410]),(⟨0,0,2⟩,[r57,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427]),(⟨0,0,3⟩,[r133,r428,r429,r430,r431,r432,r433,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443]),(⟨0,0,4⟩,[r20,r444,r445,r446,r447,r448,r449,r450,r451,r452,r453,r454,r455,r456,r457,r458]),(⟨0,0,5⟩,[r392,r459,r460,r461,r462,r463,r464,r465,r466,r467,r468,r469,r470,r471,r472]),(⟨0,0,6⟩,[0,r39,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483,r484]),(⟨0,1,0⟩,[r392,r393,r394,r395,r396,r397,r398,r399,r400,r401,r402,r403,r404,r405,r406,r407,r408,r409,r410]),(⟨0,1,1⟩,[0,r103,r485,r486,r487,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498,r499,r500]),(⟨0,1,2⟩,[r501,r502,r503,r504,r505,r506,r507,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517]),(⟨0,1,3⟩,[0,r518,r519,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531,r532]),(⟨0,1,4⟩,[0,0,r116,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543,r544]),(⟨0,2,0⟩,[r57,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427]),(⟨0,2,1⟩,[r501,r502,r503,r504,r505,r506,r507,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517]),(⟨0,2,2⟩,[r0,r545,r546,r547,r548,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558,r559]),(⟨0,2,3⟩,[r501,r560,r561,r562,r563,r564,r565,r566,r567,r568,r569,r570,r571,r572,r573]),(⟨0,2,4⟩,[0,r574,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584,r585,r586]),(⟨0,2,5⟩,[r20,r587,r588,r589,r590,r591,r592,r593,r594,r595,r596,r597,r598]),(⟨0,2,6⟩,[0,r103,r599,r600,r601,r602,r603,r604,r605,r606,r607,r608]),(⟨0,3,0⟩,[r133,r428,r429,r430,r431,r432,r433,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443]),(⟨0,3,1⟩,[0,r518,r519,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531,r532]),(⟨0,3,2⟩,[r501,r560,r561,r562,r563,r564,r565,r566,r567,r568,r569,r570,r571,r572,r573]),(⟨0,3,3⟩,[0,r178,r609,r610,r611,r612,r613,r614,r615,r616,r617,r618,r619,r620]),(⟨0,3,4⟩,[r20,r587,r588,r589,r621,r622,r623,r624,r625,r626,r627,r628,r629]),(⟨0,3,5⟩,[0,r103,r599,r600,r601,r602,r603,r604,r605,r606,r607,r608]),(⟨0,4,0⟩,[r20,r444,r445,r446,r447,r448,r449,r450,r451,r452,r453,r454,r455,r456,r457,r458]),(⟨0,4,1⟩,[0,0,r116,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543,r544]),(⟨0,4,2⟩,[0,r574,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584,r585,r586]),(⟨0,4,3⟩,[r20,r587,r588,r589,r621,r622,r623,r624,r625,r626,r627,r628,r629]),(⟨0,5,0⟩,[r392,r459,r460,r461,r462,r463,r464,r465,r466,r467,r468,r469,r470,r471,r472]),(⟨0,5,2⟩,[r20,r587,r588,r589,r590,r591,r592,r593,r594,r595,r596,r597,r598]),(⟨0,5,3⟩,[0,r103,r599,r600,r601,r602,r603,r604,r605,r606,r607,r608]),(⟨0,6,0⟩,[0,r39,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483,r484]),(⟨0,6,2⟩,[0,r103,r599,r600,r601,r602,r603,r604,r605,r606,r607,r608]),(⟨1,0,0⟩,[r392,r393,r394,r395,r396,r397,r398,r399,r400,r401,r402,r403,r404,r405,r406,r407,r408,r409,r410]),(⟨1,0,1⟩,[0,r103,r485,r486,r487,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498,r499,r500]),(⟨1,0,2⟩,[r501,r502,r503,r504,r505,r506,r507,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517]),(⟨1,0,3⟩,[0,r518,r519,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531,r532]),(⟨1,0,4⟩,[0,0,r116,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543,r544]),(⟨1,1,0⟩,[0,r103,r485,r486,r487,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498,r499,r500]),(⟨1,1,1⟩,[0,0,r630,r631,r632,r633,r634,r635,r636,r637,r638,r639,r640,r641,r642,r643,r644]),(⟨1,1,2⟩,[0,r0,r545,r645,r646,r647,r648,r649,r650,r651,r652,r653,r654,r655,r656,r657]),(⟨1,1,3⟩,[0,0,r116,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543,r544]),(⟨1,2,0⟩,[r501,r502,r503,r504,r505,r506,r507,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517]),(⟨1,2,1⟩,[0,r0,r545,r645,r646,r647,r648,r649,r650,r651,r652,r653,r654,r655,r656,r657]),(⟨1,2,3⟩,[0,r574,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584,r585,r586]),(⟨1,2,4⟩,[0,0,0,0,r658,r659,r660,r661,r662,r663,r664,r665,-524288]),(⟨1,3,0⟩,[0,r518,r519,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531,r532]),(⟨1,3,1⟩,[0,0,r116,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543,r544]),(⟨1,3,2⟩,[0,r574,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584,r585,r586]),(⟨1,3,3⟩,[0,0,0,0,r293,r294,r295,r296,r297,r298,r299,r300,-1048576]),(⟨1,4,0⟩,[0,0,r116,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543,r544]),(⟨1,4,2⟩,[0,0,0,0,r658,r659,r660,r661,r662,r663,r664,r665,-524288]),(⟨2,0,0⟩,[r57,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427]),(⟨2,0,1⟩,[r501,r502,r503,r504,r505,r506,r507,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517]),(⟨2,0,2⟩,[r0,r545,r546,r547,r548,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558,r559]),(⟨2,0,3⟩,[r501,r560,r561,r562,r563,r564,r565,r566,r567,r568,r569,r570,r571,r572,r573]),(⟨2,0,4⟩,[0,r574,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584,r585,r586]),(⟨2,0,5⟩,[r20,r587,r588,r589,r590,r591,r592,r593,r594,r595,r596,r597,r598]),(⟨2,0,6⟩,[0,r103,r599,r600,r601,r602,r603,r604,r605,r606,r607,r608]),(⟨2,1,0⟩,[r501,r502,r503,r504,r505,r506,r507,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517]),(⟨2,1,1⟩,[0,r0,r545,r645,r646,r647,r648,r649,r650,r651,r652,r653,r654,r655,r656,r657]),(⟨2,1,3⟩,[0,r574,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584,r585,r586]),(⟨2,1,4⟩,[0,0,0,0,r658,r659,r660,r661,r662,r663,r664,r665,-524288]),(⟨2,2,0⟩,[r0,r545,r546,r547,r548,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558,r559]),(⟨2,2,2⟩,[r178,r666,r667,r668,r669,r670,r671,r672,r673,r674,r675,r676,r677,r678]),(⟨2,2,3⟩,[r178,r679,r680,r681,r682,r683,r684,r685,r686,r687,r688,r689,r690]),(⟨2,2,4⟩,[r39,r691,r692,r693,r694,r695,r696,r697,r698,r699,r700,r701]),(⟨2,2,5⟩,[r57,r301,r702,r703,r704,r705,r706,r707,r708,r709,r710]),(⟨2,3,0⟩,[r501,r560,r561,r562,r563,r564,r565,r566,r567,r568,r569,r570,r571,r572,r573]),(⟨2,3,1⟩,[0,r574,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584,r585,r586]),(⟨2,3,2⟩,[r178,r679,r680,r681,r682,r683,r684,r685,r686,r687,r688,r689,r690]),(⟨2,3,3⟩,[0,r711,r712,r713,r714,r715,r716,r717,r718,r719,r720,r721]),(⟨2,4,0⟩,[0,r574,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584,r585,r586]),(⟨2,4,1⟩,[0,0,0,0,r658,r659,r660,r661,r662,r663,r664,r665,-524288]),(⟨2,4,2⟩,[r39,r691,r692,r693,r694,r695,r696,r697,r698,r699,r700,r701]),(⟨2,4,5⟩,[r39,r722,r723,r724,r725,r726,r727,r728,131072]),(⟨2,5,0⟩,[r20,r587,r588,r589,r590,r591,r592,r593,r594,r595,r596,r597,r598]),(⟨2,5,2⟩,[r57,r301,r702,r703,r704,r705,r706,r707,r708,r709,r710]),(⟨2,5,4⟩,[r39,r722,r723,r724,r725,r726,r727,r728,131072]),(⟨2,6,0⟩,[0,r103,r599,r600,r601,r602,r603,r604,r605,r606,r607,r608]),(⟨3,0,0⟩,[r133,r428,r429,r430,r431,r432,r433,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443]),(⟨3,0,1⟩,[0,r518,r519,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531,r532]),(⟨3,0,2⟩,[r501,r560,r561,r562,r563,r564,r565,r566,r567,r568,r569,r570,r571,r572,r573]),(⟨3,0,3⟩,[0,r178,r609,r610,r611,r612,r613,r614,r615,r616,r617,r618,r619,r620]),(⟨3,0,4⟩,[r20,r587,r588,r589,r621,r622,r623,r624,r625,r626,r627,r628,r629]),(⟨3,0,5⟩,[0,r103,r599,r600,r601,r602,r603,r604,r605,r606,r607,r608]),(⟨3,1,0⟩,[0,r518,r519,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531,r532]),(⟨3,1,1⟩,[0,0,r116,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543,r544]),(⟨3,1,2⟩,[0,r574,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584,r585,r586]),(⟨3,1,3⟩,[0,0,0,0,r293,r294,r295,r296,r297,r298,r299,r300,-1048576]),(⟨3,2,0⟩,[r501,r560,r561,r562,r563,r564,r565,r566,r567,r568,r569,r570,r571,r572,r573]),(⟨3,2,1⟩,[0,r574,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584,r585,r586]),(⟨3,2,2⟩,[r178,r679,r680,r681,r682,r683,r684,r685,r686,r687,r688,r689,r690]),(⟨3,2,3⟩,[0,r711,r712,r713,r714,r715,r716,r717,r718,r719,r720,r721]),(⟨3,3,0⟩,[0,r178,r609,r610,r611,r612,r613,r614,r615,r616,r617,r618,r619,r620]),(⟨3,3,1⟩,[0,0,0,0,r293,r294,r295,r296,r297,r298,r299,r300,-1048576]),(⟨3,3,2⟩,[0,r711,r712,r713,r714,r715,r716,r717,r718,r719,r720,r721]),(⟨3,4,0⟩,[r20,r587,r588,r589,r621,r622,r623,r624,r625,r626,r627,r628,r629]),(⟨3,5,0⟩,[0,r103,r599,r600,r601,r602,r603,r604,r605,r606,r607,r608]),(⟨4,0,0⟩,[r20,r444,r445,r446,r447,r448,r449,r450,r451,r452,r453,r454,r455,r456,r457,r458]),(⟨4,0,1⟩,[0,0,r116,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543,r544]),(⟨4,0,2⟩,[0,r574,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584,r585,r586]),(⟨4,0,3⟩,[r20,r587,r588,r589,r621,r622,r623,r624,r625,r626,r627,r628,r629]),(⟨4,1,0⟩,[0,0,r116,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543,r544]),(⟨4,1,2⟩,[0,0,0,0,r658,r659,r660,r661,r662,r663,r664,r665,-524288]),(⟨4,2,0⟩,[0,r574,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584,r585,r586]),(⟨4,2,1⟩,[0,0,0,0,r658,r659,r660,r661,r662,r663,r664,r665,-524288]),(⟨4,2,2⟩,[r39,r691,r692,r693,r694,r695,r696,r697,r698,r699,r700,r701]),(⟨4,2,5⟩,[r39,r722,r723,r724,r725,r726,r727,r728,131072]),(⟨4,3,0⟩,[r20,r587,r588,r589,r621,r622,r623,r624,r625,r626,r627,r628,r629]),(⟨4,5,2⟩,[r39,r722,r723,r724,r725,r726,r727,r728,131072]),(⟨5,0,0⟩,[r392,r459,r460,r461,r462,r463,r464,r465,r466,r467,r468,r469,r470,r471,r472]),(⟨5,0,2⟩,[r20,r587,r588,r589,r590,r591,r592,r593,r594,r595,r596,r597,r598]),(⟨5,0,3⟩,[0,r103,r599,r600,r601,r602,r603,r604,r605,r606,r607,r608]),(⟨5,2,0⟩,[r20,r587,r588,r589,r590,r591,r592,r593,r594,r595,r596,r597,r598]),(⟨5,2,2⟩,[r57,r301,r702,r703,r704,r705,r706,r707,r708,r709,r710]),(⟨5,2,4⟩,[r39,r722,r723,r724,r725,r726,r727,r728,131072]),(⟨5,3,0⟩,[0,r103,r599,r600,r601,r602,r603,r604,r605,r606,r607,r608]),(⟨5,4,2⟩,[r39,r722,r723,r724,r725,r726,r727,r728,131072]),(⟨6,0,0⟩,[0,r39,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483,r484]),(⟨6,0,2⟩,[0,r103,r599,r600,r601,r602,r603,r604,r605,r606,r607,r608]),(⟨6,2,0⟩,[0,r103,r599,r600,r601,r602,r603,r604,r605,r606,r607,r608])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[128,-2368,16192,-48960,27712,296128,-1096256,1862976,-1545664,318080]),(⟨0,0,1⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨0,0,2⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨0,0,3⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨0,1,0⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨0,1,1⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248]),(⟨0,2,0⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨0,2,3⟩,[-128,1536,-3840,-4608,15232]),(⟨0,3,0⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨0,3,2⟩,[-128,1536,-3840,-4608,15232]),(⟨1,0,0⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨1,0,1⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248]),(⟨1,1,0⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248]),(⟨2,0,0⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨2,0,3⟩,[-128,1536,-3840,-4608,15232]),(⟨2,3,0⟩,[-128,1536,-3840,-4608,15232]),(⟨3,0,0⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨3,0,2⟩,[-128,1536,-3840,-4608,15232]),(⟨3,2,0⟩,[-128,1536,-3840,-4608,15232])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[-256,5120,-43008,199936,-545280,801024,-457728,253696,-1684736,2508544,-513024]),(⟨0,0,1⟩,[0,1536,-21760,121088,-327424,405248,-133888,235264,-1327360,1571584]),(⟨0,0,2⟩,[256,-4608,28416,-75264,67840,43520,25856,-250368,-32256]),(⟨0,0,3⟩,[0,-2048,20992,-74240,87040,37888,31232,-363008]),(⟨0,1,0⟩,[0,1536,-21760,121088,-327424,405248,-133888,235264,-1327360,1571584]),(⟨0,1,1⟩,[0,0,0,0,4096,-49152,122880,147456,-487424]),(⟨0,2,0⟩,[256,-4608,28416,-75264,67840,43520,25856,-250368,-32256]),(⟨0,3,0⟩,[0,-2048,20992,-74240,87040,37888,31232,-363008]),(⟨1,0,0⟩,[0,1536,-21760,121088,-327424,405248,-133888,235264,-1327360,1571584]),(⟨1,0,1⟩,[0,0,0,0,4096,-49152,122880,147456,-487424]),(⟨1,1,0⟩,[0,0,0,0,4096,-49152,122880,147456,-487424]),(⟨2,0,0⟩,[256,-4608,28416,-75264,67840,43520,25856,-250368,-32256]),(⟨2,2,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨3,0,0⟩,[0,-2048,20992,-74240,87040,37888,31232,-363008])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 7 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r729) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 13 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r729) sourceRight))).isZero := by decide +kernel

noncomputable def partial19 : Poly := []

theorem partial_sound19 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 19)
      sourceRight).eval u v t=partial19.eval u v t := by rfl

noncomputable def chunk16 : Poly := [(⟨3,0,0⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨3,0,2⟩,[-128,1536,-3840,-4608,15232]),(⟨3,2,0⟩,[-128,1536,-3840,-4608,15232])]

noncomputable def partial16 : Poly := [(⟨3,0,0⟩,[16384,-655360,10928128,-100941824,565395456,-1871839232,2447425536,8137457664,-52265893888,137571598336,-209690148864,195748118528,-179390005248,374880862208,-658501910528,522787307520,-93083074560]),(⟨3,0,1⟩,[0,-98304,3358720,-45334528,317751296,-1201799168,1772077056,4770742272,-31743344640,78959640576,-107578474496,87957684224,-108458639360,285376708608,-448033832960,285148200960]),(⟨3,0,2⟩,[16384,-425984,5013504,-39092224,233062400,-1030225920,3115876352,-6130565120,7995965440,-8686829568,9495347200,-5172264960,1059241984,-599982080,-13666910208]),(⟨3,0,3⟩,[0,-65536,1179648,-10223616,65536000,-351207424,1486618624,-4729602048,10970726400,-17287282688,15600844800,-9213575168,26065502208,-41925804032]),(⟨3,0,4⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨3,0,5⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨3,1,0⟩,[0,-98304,3358720,-45334528,317751296,-1201799168,1772077056,4770742272,-31743344640,78959640576,-107578474496,87957684224,-108458639360,285376708608,-448033832960,285148200960]),(⟨3,1,1⟩,[0,0,0,0,-262144,8388608,-96731136,469762048,-508035072,-3900702720,15981871104,-20015218688,-18139578368,91016396800,-88438210560]),(⟨3,1,2⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨3,1,3⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨3,2,0⟩,[16384,-425984,5013504,-39092224,233062400,-1030225920,3115876352,-6130565120,7995965440,-8686829568,9495347200,-5172264960,1059241984,-599982080,-13666910208]),(⟨3,2,1⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨3,2,2⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨3,2,3⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨3,3,0⟩,[0,-65536,1179648,-10223616,65536000,-351207424,1486618624,-4729602048,10970726400,-17287282688,15600844800,-9213575168,26065502208,-41925804032]),(⟨3,3,1⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨3,3,2⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨3,4,0⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨3,5,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨4,0,0⟩,[0,-98304,3358720,-45334528,317751296,-1201799168,1772077056,4770742272,-31743344640,78959640576,-107578474496,87957684224,-108458639360,285376708608,-448033832960,285148200960]),(⟨4,0,1⟩,[0,0,0,0,-262144,8388608,-96731136,469762048,-508035072,-3900702720,15981871104,-20015218688,-18139578368,91016396800,-88438210560]),(⟨4,0,2⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨4,0,3⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨4,1,0⟩,[0,0,0,0,-262144,8388608,-96731136,469762048,-508035072,-3900702720,15981871104,-20015218688,-18139578368,91016396800,-88438210560]),(⟨4,1,2⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨4,2,0⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨4,2,1⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨4,3,0⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨5,0,0⟩,[-16384,622592,-9338880,71041024,-281493504,401440768,1309442048,-7877165056,17629790208,-19114196992,7248314368,-6379012096,36310499328,-41174138880,-5852528640]),(⟨5,0,2⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨5,2,0⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨5,2,2⟩,[65536,-2097152,24182784,-117440512,127008768,975175680,-3995467776,5003804672,4534894592,-22754099200,22109552640]),(⟨5,2,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨5,4,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨6,0,0⟩,[0,131072,-3964928,44597248,-238845952,544899072,479133696,-6290866176,16780034048,-20933574656,11213307904,-12878708736,53525708800,-65864171520]),(⟨6,0,2⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨6,2,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856])]


theorem partial_checked16 :
    (Poly.add (Poly.add (Poly.mul chunk16 sourceRight) partial19)
      (Poly.scale (K.ofRat (-1)) partial16)).isZero := by decide +kernel

theorem partial_sound16 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 16)
      sourceRight).eval u v t=partial16.eval u v t := by
  change (Poly.mul (chunk16++(sourceLeft.drop 19))
    sourceRight).eval u v t=partial16.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound19 partial_checked16 u v t


noncomputable def chunk12 : Poly := [(⟨1,1,0⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248]),(⟨2,0,0⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨2,0,3⟩,[-128,1536,-3840,-4608,15232]),(⟨2,3,0⟩,[-128,1536,-3840,-4608,15232])]

noncomputable def partial12 : Poly := [(⟨1,1,0⟩,[0,65536,-2228224,33357824,-292356096,1670578176,-6463422464,16543318016,-23775870976,-963969024,83842433024,-172088950784,139408506880,-43871043584,239047802880,-671442993152,599295721472,-109401341952]),(⟨1,1,1⟩,[0,0,-393216,11075584,-132972544,900071424,-3777232896,9860743168,-13452902400,-3758882816,52387512320,-87140401152,40828207104,-8155430912,209029431296,-480196362240,335137144832]),(⟨1,1,2⟩,[0,-65536,2097152,-27787264,200146944,-859504640,2183266304,-2496528384,-2828271616,15081209856,-20262420480,2463367168,6363152384,37076795392,-49344282624,-6878527488]),(⟨1,1,3⟩,[0,0,524288,-12713984,126222336,-672792576,2051932160,-3129212928,-689176576,12624592896,-20401881088,3620077568,5927469056,52195885056,-77410729984]),(⟨1,2,0⟩,[0,0,-393216,11075584,-132972544,900071424,-3777232896,9860743168,-13452902400,-3758882816,52387512320,-87140401152,40828207104,-8155430912,209029431296,-480196362240,335137144832]),(⟨1,2,1⟩,[0,0,0,0,0,-1048576,27262976,-271581184,1283457024,-2644508672,-926941184,18129879040,-40089157632,10077863936,92587163648,-103942193152]),(⟨1,3,0⟩,[0,-65536,2097152,-27787264,200146944,-859504640,2183266304,-2496528384,-2828271616,15081209856,-20262420480,2463367168,6363152384,37076795392,-49344282624,-6878527488]),(⟨1,4,0⟩,[0,0,524288,-12713984,126222336,-672792576,2051932160,-3129212928,-689176576,12624592896,-20401881088,3620077568,5927469056,52195885056,-77410729984]),(⟨2,0,0⟩,[32768,-1114112,16285696,-133955584,669351936,-1924333568,1604517888,11151605760,-55072129024,130821062656,-192265420800,194586607616,-206086111232,368167026688,-590822899712,499122700288,-142179532800,12411076608]),(⟨2,0,1⟩,[0,-196608,5537792,-64126976,390463488,-1255899136,1202388992,6739394560,-32959463424,73496920064,-98182201344,93425991680,-126258315264,269789986816,-400000417792,281754468352,-38019760128]),(⟨2,0,2⟩,[-32768,1048576,-13500416,88637440,-294944768,249593856,1810759680,-8021868544,15869575168,-17077043200,9741402112,-9468608512,30757781504,-36630528000,933101568,780337152]),(⟨2,0,3⟩,[32768,-786432,7995392,-50167808,245268480,-978812928,2792554496,-4949475328,5560172544,-8067678208,16083058688,-15671984128,11169398784,-17844502528,967507968]),(⟨2,0,4⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨2,0,5⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨2,0,6⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨2,1,0⟩,[0,-196608,5144576,-53051392,257490944,-355827712,-2574843904,16600137728,-46412365824,69738037248,-45794689024,6285590528,-85430108160,261634555904,-190970986496,-198441893888,297117384704]),(⟨2,1,1⟩,[0,0,0,0,-524288,12582912,-102236160,224919552,1190133760,-7635730432,13850640384,4402970624,-59616264192,87428169728,11593580544,-92150431744]),(⟨2,1,3⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨2,1,4⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨2,2,0⟩,[-32768,1048576,-13500416,88637440,-294944768,248545280,1838022656,-8293449728,17153032192,-19721551872,8814460928,8661270528,-9331376128,-26552664064,93520265216,-103161856000]),(⟨2,2,3⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨2,3,0⟩,[32768,-786432,7995392,-50167808,245268480,-978812928,2792554496,-4949475328,5560172544,-8067678208,16083058688,-15671984128,11169398784,-17844502528,967507968]),(⟨2,3,1⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨2,3,2⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨2,3,3⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨2,4,0⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨2,4,1⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨2,5,0⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨2,6,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨3,0,0⟩,[16384,-851968,16465920,-165068800,955858944,-3127738368,3649814528,14876852224,-85225357312,211068518400,-307872350208,289174110208,-305648320512,644670849024,-1058502328320,804541775872,-131102834688]),(⟨3,0,1⟩,[0,-98304,3358720,-45334528,317227008,-1188167680,1642577920,5267243008,-31836667904,73968418816,-92800892928,74230775808,-127985745920,362727014400,-529027416064,296939962368]),(⟨3,0,2⟩,[16384,-425984,5013504,-39092224,233062400,-1030225920,3115876352,-6130565120,7995965440,-8686829568,9495347200,-5172264960,1059241984,-599982080,-13666910208]),(⟨3,0,3⟩,[0,-262144,6324224,-65044480,369917952,-1247313920,2494103552,-3168337920,5161418752,-13640990720,19988381696,-5548441600,-1394704384,-17987436544]),(⟨3,0,4⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨3,0,5⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨3,1,0⟩,[0,-163840,5455872,-73121792,517373952,-2047672320,3825844224,2770714624,-34664939520,89049628672,-113063313408,76694142976,-121622593536,399803809792,-578371698688,290061434880]),(⟨3,1,1⟩,[0,0,0,0,-262144,8388608,-96731136,469762048,-508035072,-3900702720,15981871104,-20015218688,-18139578368,91016396800,-88438210560]),(⟨3,1,2⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨3,1,3⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨3,2,0⟩,[16384,-425984,5013504,-39092224,233062400,-1030225920,3115876352,-6130565120,7995965440,-8686829568,9495347200,-5172264960,1059241984,-599982080,-13666910208]),(⟨3,2,1⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨3,2,2⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨3,2,3⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨3,3,0⟩,[0,-262144,6324224,-65044480,369917952,-1247313920,2494103552,-3168337920,5161418752,-13640990720,19988381696,-5548441600,-1394704384,-17987436544]),(⟨3,3,1⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨3,3,2⟩,[0,524288,-12648448,117506048,-517210112,947126272,613548032,-6115426304,10495983616,-692322304,-20998324224,20456210432]),(⟨3,4,0⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨3,5,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨4,0,0⟩,[-32768,950272,-10141696,43302912,22806528,-952205312,3582836736,-3251126272,-15873769472,61882597376,-97837072384,78489075712,-77700857856,248746180608,-447100731392,285928538112]),(⟨4,0,1⟩,[0,0,0,0,-262144,8388608,-96731136,469762048,-508035072,-3900702720,15981871104,-20015218688,-18139578368,91016396800,-88438210560]),(⟨4,0,2⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨4,0,3⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨4,1,0⟩,[0,0,524288,-12713984,125960192,-664403968,1955201024,-2659450880,-1197211648,8723890176,-4420009984,-16395141120,-12212109312,143212281856,-165848940544]),(⟨4,1,2⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨4,2,0⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨4,2,1⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨4,2,2⟩,[131072,-3407872,32374784,-124125184,23330816,1247805440,-3694395392,3431727104,4881776640,-19337576448,20248395776,-2947940352]),(⟨4,2,5⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,3,0⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨4,5,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨5,0,0⟩,[-16384,884736,-15695872,131006464,-550780928,854294528,2295562240,-14573240320,32823787520,-37609242624,21084340224,-23257743360,82731155456,-99592798208,2929360896]),(⟨5,0,2⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨5,0,3⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨5,2,0⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨5,2,2⟩,[65536,-2097152,24182784,-117440512,127008768,975175680,-3995467776,5003804672,4534894592,-22754099200,22109552640]),(⟨5,2,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨5,3,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨5,4,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨6,0,0⟩,[0,131072,-3964928,44597248,-238845952,544899072,479133696,-6290866176,16780034048,-20933574656,11213307904,-12878708736,53525708800,-65864171520]),(⟨6,0,2⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨6,2,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial16)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 16))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound16 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨0,3,0⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨0,3,2⟩,[-128,1536,-3840,-4608,15232]),(⟨1,0,0⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨1,0,1⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248])]

noncomputable def partial8 : Poly := [(⟨0,3,0⟩,[16384,-655360,10928128,-100941824,565395456,-1871839232,2447425536,8137457664,-52265893888,137571598336,-209690148864,195748118528,-179390005248,374880862208,-658501910528,522787307520,-93083074560]),(⟨0,3,1⟩,[0,-98304,3358720,-45334528,317751296,-1201799168,1772077056,4770742272,-31743344640,78959640576,-107578474496,87957684224,-108458639360,285376708608,-448033832960,285148200960]),(⟨0,3,2⟩,[16384,-425984,5013504,-39092224,233062400,-1030225920,3115876352,-6130565120,7995965440,-8686829568,9495347200,-5172264960,1059241984,-599982080,-13666910208]),(⟨0,3,3⟩,[0,-65536,1179648,-10223616,65536000,-351207424,1486618624,-4729602048,10970726400,-17287282688,15600844800,-9213575168,26065502208,-41925804032]),(⟨0,3,4⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨0,3,5⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨0,4,0⟩,[0,-98304,3358720,-45334528,317751296,-1201799168,1772077056,4770742272,-31743344640,78959640576,-107578474496,87957684224,-108458639360,285376708608,-448033832960,285148200960]),(⟨0,4,1⟩,[0,0,0,0,-262144,8388608,-96731136,469762048,-508035072,-3900702720,15981871104,-20015218688,-18139578368,91016396800,-88438210560]),(⟨0,4,2⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨0,4,3⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨0,5,0⟩,[-16384,622592,-9338880,71041024,-281493504,401440768,1309442048,-7877165056,17629790208,-19114196992,7248314368,-6379012096,36310499328,-41174138880,-5852528640]),(⟨0,5,2⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨0,6,0⟩,[0,131072,-3964928,44597248,-238845952,544899072,479133696,-6290866176,16780034048,-20933574656,11213307904,-12878708736,53525708800,-65864171520]),(⟨0,6,2⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨1,0,0⟩,[-16384,704512,-13271040,145883136,-1042006016,5021270016,-15898509312,26999357440,16291610624,-245644623872,764025405440,-1380770316288,1641148039168,-1613520273408,2345695772672,-4142652227584,4828123758592,-2777716637696,442431897600]),(⟨1,0,1⟩,[0,163840,-5881856,91029504,-805863424,4505026560,-16172138496,33727741952,-14225506304,-149834317824,524798640128,-906478747648,936804450304,-904680783872,1876214497280,-3601026613248,3625989111808,-1464735383552]),(⟨1,0,2⟩,[16384,-671744,11190272,-99385344,504709120,-1316077568,-72335360,13671530496,-51807764480,98407694336,-93142040576,24579112960,-29935484928,160700940288,-89745539072,-302905688064,362954719232]),(⟨1,0,3⟩,[0,-196608,6455296,-87293952,640647168,-2753658880,6459097088,-2970386432,-31213289472,107052924928,-168030470144,136080457728,-110491238400,304469409792,-510982291456,306179571712]),(⟨1,0,4⟩,[0,0,524288,-12713984,126222336,-672792576,2051932160,-3129212928,-689176576,12624592896,-20401881088,3620077568,5927469056,52195885056,-77410729984]),(⟨1,1,0⟩,[0,163840,-5881856,91029504,-805863424,4505026560,-16172138496,33727741952,-14225506304,-149834317824,524798640128,-906478747648,936804450304,-904680783872,1876214497280,-3601026613248,3625989111808,-1464735383552]),(⟨1,1,1⟩,[0,0,-786432,22151168,-265682944,1790967808,-7426539520,18815254528,-23631364096,-10952376320,85875490816,-87455039488,-60581085184,-20160970752,841358508032,-1671250968576,1090628747264]),(⟨1,1,2⟩,[0,-65536,2097152,-27787264,200146944,-860553216,2210529280,-2768109568,-1544814592,12436701184,-21189361664,20593246208,-33726005248,47154659328,43242881024,-110820720640]),(⟨1,1,3⟩,[0,0,524288,-12713984,126222336,-672792576,2051932160,-3129212928,-689176576,12624592896,-20401881088,3620077568,5927469056,52195885056,-77410729984]),(⟨1,2,0⟩,[16384,-671744,11190272,-99385344,504709120,-1316077568,-72335360,13671530496,-51807764480,98407694336,-93142040576,24579112960,-29935484928,160700940288,-89745539072,-302905688064,362954719232]),(⟨1,2,1⟩,[0,-65536,2097152,-27787264,200146944,-860553216,2210529280,-2768109568,-1544814592,12436701184,-21189361664,20593246208,-33726005248,47154659328,43242881024,-110820720640]),(⟨1,3,0⟩,[0,-294912,9814016,-132628480,958398464,-3955458048,8231174144,1800355840,-62956634112,186012565504,-275608944640,224038141952,-218949877760,589846118400,-959016124416,591327772672]),(⟨1,3,1⟩,[0,0,524288,-12713984,125960192,-664403968,1955201024,-2659450880,-1197211648,8723890176,-4420009984,-16395141120,-12212109312,143212281856,-165848940544]),(⟨1,3,2⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨1,3,3⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨1,4,0⟩,[0,0,524288,-12713984,125960192,-664403968,1955201024,-2659450880,-1197211648,8723890176,-4420009984,-16395141120,-12212109312,143212281856,-165848940544]),(⟨1,4,2⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨2,0,0⟩,[32768,-1015808,12632064,-76283904,155844608,910114816,-8104198144,28336029696,-45521764352,-18049286144,248690786304,-539803189248,591309832192,-492642713600,1046343794688,-2430460919808,2884513857536,-1342922964992]),(⟨2,0,1⟩,[0,-196608,5144576,-53051392,257753088,-365002752,-2446917632,15693905920,-43137925120,66303426560,-64694222848,93111353344,-227667607552,257784446976,232328658944,-909300137984,717471842304]),(⟨2,0,2⟩,[-32768,1048576,-13500416,88637440,-294944768,248545280,1838022656,-8293449728,17153032192,-19721551872,8814460928,8661270528,-9331376128,-26552664064,93520265216,-103161856000]),(⟨2,0,3⟩,[32768,-786432,7995392,-50167808,245268480,-978812928,2792554496,-4949475328,5560172544,-8067678208,16083058688,-15671984128,11169398784,-17844502528,967507968]),(⟨2,0,4⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨2,0,5⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨2,0,6⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨2,1,0⟩,[0,-196608,5144576,-53051392,257753088,-365002752,-2446917632,15693905920,-43137925120,66303426560,-64694222848,93111353344,-227667607552,257784446976,232328658944,-909300137984,717471842304]),(⟨2,1,1⟩,[0,0,0,0,-524288,11534336,-74973184,-46661632,2473590784,-10280239104,12923699200,22532849664,-99705421824,97506033664,104180744192,-196092624896]),(⟨2,1,3⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨2,1,4⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨2,2,0⟩,[-32768,1048576,-13500416,88637440,-294944768,248545280,1838022656,-8293449728,17153032192,-19721551872,8814460928,8661270528,-9331376128,-26552664064,93520265216,-103161856000]),(⟨2,2,3⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨2,3,0⟩,[16384,-163840,-1343488,20873216,-36225024,-577372160,4101996544,-12826640384,23189962752,-27181875200,23331373056,-22050996224,47479898112,-59018641408,-4885020672]),(⟨2,3,1⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨2,3,2⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨2,3,3⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨2,4,0⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨2,4,1⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨2,5,0⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨2,5,2⟩,[65536,-2097152,24182784,-117440512,127008768,975175680,-3995467776,5003804672,4534894592,-22754099200,22109552640]),(⟨2,5,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,6,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨3,0,0⟩,[32768,-1523712,28049408,-275529728,1593540608,-5343887360,7354712064,18687639552,-123580219392,313235095552,-453401903104,400893624320,-376412012544,813527220224,-1357277298688,981832450048,-103285260288]),(⟨3,0,1⟩,[0,-163840,5455872,-73121792,517373952,-2047672320,3825844224,2770714624,-34664939520,89049628672,-113063313408,76694142976,-121622593536,399803809792,-578371698688,290061434880]),(⟨3,0,2⟩,[16384,-425984,5013504,-39092224,233062400,-1030225920,3115876352,-6130565120,7995965440,-8686829568,9495347200,-5172264960,1059241984,-599982080,-13666910208]),(⟨3,0,3⟩,[0,-262144,6324224,-65044480,369917952,-1247313920,2494103552,-3168337920,5161418752,-13640990720,19988381696,-5548441600,-1394704384,-17987436544]),(⟨3,0,4⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨3,0,5⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨3,1,0⟩,[0,-163840,5455872,-73121792,517373952,-2047672320,3825844224,2770714624,-34664939520,89049628672,-113063313408,76694142976,-121622593536,399803809792,-578371698688,290061434880]),(⟨3,1,1⟩,[0,0,0,0,-262144,8388608,-96731136,469762048,-508035072,-3900702720,15981871104,-20015218688,-18139578368,91016396800,-88438210560]),(⟨3,1,2⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨3,1,3⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨3,2,0⟩,[16384,-425984,5013504,-39092224,233062400,-1030225920,3115876352,-6130565120,7995965440,-8686829568,9495347200,-5172264960,1059241984,-599982080,-13666910208]),(⟨3,2,1⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨3,2,2⟩,[-131072,4259840,-55377920,366149632,-1235156992,1231683584,5890244608,-24815206400,36265525248,3873767424,-102482116608,170384621568,-106071261184]),(⟨3,2,3⟩,[0,524288,-12648448,117506048,-517210112,947126272,613548032,-6115426304,10495983616,-692322304,-20998324224,20456210432]),(⟨3,3,0⟩,[0,-131072,2359296,-20447232,131072000,-702414848,2973237248,-9459204096,21941452800,-34574565376,31201689600,-18427150336,52131004416,-83851608064]),(⟨3,3,1⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨3,3,2⟩,[0,786432,-18481152,167116800,-713555968,1233125376,995360768,-7698382848,10969677824,1134821376,-18849857536,14926872576]),(⟨3,4,0⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨3,5,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨4,0,0⟩,[-32768,819200,-5783552,-16203776,463306752,-2846359552,7858667520,-3724984320,-44258787328,153854312448,-245605122048,212106166272,-194555248640,516138795008,-908738740224,598986637312]),(⟨4,0,1⟩,[0,0,524288,-12713984,125960192,-664403968,1955201024,-2659450880,-1197211648,8723890176,-4420009984,-16395141120,-12212109312,143212281856,-165848940544]),(⟨4,0,2⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨4,0,3⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨4,1,0⟩,[0,0,524288,-12713984,125960192,-664403968,1955201024,-2659450880,-1197211648,8723890176,-4420009984,-16395141120,-12212109312,143212281856,-165848940544]),(⟨4,1,2⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨4,2,0⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨4,2,1⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨4,2,2⟩,[131072,-3407872,32374784,-124125184,23330816,1247805440,-3694395392,3431727104,4881776640,-19337576448,20248395776,-2947940352]),(⟨4,2,5⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,3,0⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨4,5,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨5,0,0⟩,[-16384,884736,-15695872,131006464,-550780928,854294528,2295562240,-14573240320,32823787520,-37609242624,21084340224,-23257743360,82731155456,-99592798208,2929360896]),(⟨5,0,2⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨5,0,3⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨5,2,0⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨5,2,2⟩,[65536,-2097152,24182784,-117440512,127008768,975175680,-3995467776,5003804672,4534894592,-22754099200,22109552640]),(⟨5,2,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨5,3,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨5,4,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨6,0,0⟩,[0,131072,-3964928,44597248,-238845952,544899072,479133696,-6290866176,16780034048,-20933574656,11213307904,-12878708736,53525708800,-65864171520]),(⟨6,0,2⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨6,2,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,1,0⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨0,1,1⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248]),(⟨0,2,0⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨0,2,3⟩,[-128,1536,-3840,-4608,15232])]

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[-16384,704512,-13271040,145883136,-1042006016,5021270016,-15898509312,26999357440,16291610624,-245644623872,764025405440,-1380770316288,1641148039168,-1613520273408,2345695772672,-4142652227584,4828123758592,-2777716637696,442431897600]),(⟨0,1,1⟩,[0,163840,-5881856,91029504,-805863424,4505026560,-16172138496,33727741952,-14225506304,-149834317824,524798640128,-906478747648,936804450304,-904680783872,1876214497280,-3601026613248,3625989111808,-1464735383552]),(⟨0,1,2⟩,[16384,-671744,11190272,-99385344,504709120,-1316077568,-72335360,13671530496,-51807764480,98407694336,-93142040576,24579112960,-29935484928,160700940288,-89745539072,-302905688064,362954719232]),(⟨0,1,3⟩,[0,-196608,6455296,-87293952,640647168,-2753658880,6459097088,-2970386432,-31213289472,107052924928,-168030470144,136080457728,-110491238400,304469409792,-510982291456,306179571712]),(⟨0,1,4⟩,[0,0,524288,-12713984,126222336,-672792576,2051932160,-3129212928,-689176576,12624592896,-20401881088,3620077568,5927469056,52195885056,-77410729984]),(⟨0,2,0⟩,[32768,-1015808,12632064,-76283904,155844608,910114816,-8104198144,28336029696,-45521764352,-18049286144,248690786304,-539803189248,591309832192,-492642713600,1046343794688,-2430460919808,2884513857536,-1342922964992]),(⟨0,2,1⟩,[0,-196608,5144576,-53051392,257753088,-365002752,-2446917632,15693905920,-43137925120,66303426560,-64694222848,93111353344,-227667607552,257784446976,232328658944,-909300137984,717471842304]),(⟨0,2,2⟩,[-32768,1048576,-13500416,88637440,-294944768,248545280,1838022656,-8293449728,17153032192,-19721551872,8814460928,8661270528,-9331376128,-26552664064,93520265216,-103161856000]),(⟨0,2,3⟩,[32768,-786432,7995392,-50167808,245268480,-978812928,2792554496,-4949475328,5560172544,-8067678208,16083058688,-15671984128,11169398784,-17844502528,967507968]),(⟨0,2,4⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨0,2,5⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨0,2,6⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨0,3,0⟩,[32768,-1523712,28049408,-275529728,1593540608,-5343887360,7354712064,18687639552,-123580219392,313235095552,-453401903104,400893624320,-376412012544,813527220224,-1357277298688,981832450048,-103285260288]),(⟨0,3,1⟩,[0,-163840,5455872,-73121792,517373952,-2047672320,3825844224,2770714624,-34664939520,89049628672,-113063313408,76694142976,-121622593536,399803809792,-578371698688,290061434880]),(⟨0,3,2⟩,[16384,-425984,5013504,-39092224,233062400,-1030225920,3115876352,-6130565120,7995965440,-8686829568,9495347200,-5172264960,1059241984,-599982080,-13666910208]),(⟨0,3,3⟩,[0,-262144,6324224,-65044480,369917952,-1247313920,2494103552,-3168337920,5161418752,-13640990720,19988381696,-5548441600,-1394704384,-17987436544]),(⟨0,3,4⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨0,3,5⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨0,4,0⟩,[-32768,819200,-5783552,-16203776,463306752,-2846359552,7858667520,-3724984320,-44258787328,153854312448,-245605122048,212106166272,-194555248640,516138795008,-908738740224,598986637312]),(⟨0,4,1⟩,[0,0,524288,-12713984,125960192,-664403968,1955201024,-2659450880,-1197211648,8723890176,-4420009984,-16395141120,-12212109312,143212281856,-165848940544]),(⟨0,4,2⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨0,4,3⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨0,5,0⟩,[-16384,884736,-15695872,131006464,-550780928,854294528,2295562240,-14573240320,32823787520,-37609242624,21084340224,-23257743360,82731155456,-99592798208,2929360896]),(⟨0,5,2⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨0,5,3⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨0,6,0⟩,[0,131072,-3964928,44597248,-238845952,544899072,479133696,-6290866176,16780034048,-20933574656,11213307904,-12878708736,53525708800,-65864171520]),(⟨0,6,2⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨1,0,0⟩,[-16384,704512,-13271040,145883136,-1042006016,5021270016,-15898509312,26999357440,16291610624,-245644623872,764025405440,-1380770316288,1641148039168,-1613520273408,2345695772672,-4142652227584,4828123758592,-2777716637696,442431897600]),(⟨1,0,1⟩,[0,163840,-5881856,91029504,-805863424,4505026560,-16172138496,33727741952,-14225506304,-149834317824,524798640128,-906478747648,936804450304,-904680783872,1876214497280,-3601026613248,3625989111808,-1464735383552]),(⟨1,0,2⟩,[16384,-671744,11190272,-99385344,504709120,-1316077568,-72335360,13671530496,-51807764480,98407694336,-93142040576,24579112960,-29935484928,160700940288,-89745539072,-302905688064,362954719232]),(⟨1,0,3⟩,[0,-196608,6455296,-87293952,640647168,-2753658880,6459097088,-2970386432,-31213289472,107052924928,-168030470144,136080457728,-110491238400,304469409792,-510982291456,306179571712]),(⟨1,0,4⟩,[0,0,524288,-12713984,126222336,-672792576,2051932160,-3129212928,-689176576,12624592896,-20401881088,3620077568,5927469056,52195885056,-77410729984]),(⟨1,1,0⟩,[0,262144,-9535488,148701184,-1319370752,7339474944,-25880854528,50912165888,-4675141632,-298704666624,965754847232,-1640868544512,1734200393728,-1765490524160,3513381191680,-6530610233344,6652682502144,-2820069425152]),(⟨1,1,1⟩,[0,0,-1179648,33226752,-398393344,2681864192,-11075846144,27769765888,-33809825792,-18145869824,119363469312,-87769677824,-161990377472,-32166510592,1473687584768,-2862305574912,1846120349696]),(⟨1,1,2⟩,[0,-65536,2097152,-27787264,200146944,-861601792,2237792256,-3039690752,-261357568,9792192512,-22116302848,38723125248,-73815162880,57232523264,135830044672,-214762913792]),(⟨1,1,3⟩,[0,0,524288,-12713984,126222336,-672792576,2051932160,-3129212928,-689176576,12624592896,-20401881088,3620077568,5927469056,52195885056,-77410729984]),(⟨1,2,0⟩,[16384,-868352,16728064,-163512320,895434752,-2581151744,1257979904,19504693248,-81492787200,168470003712,-210223775744,204830867456,-298431299584,426640818176,-66446311424,-732009463808,745289416704]),(⟨1,2,1⟩,[0,-65536,2097152,-27787264,199622656,-847970304,2108293120,-2543190016,-354680832,4800970752,-7338721280,24996216832,-93342269440,134582829056,54836461568,-202971152384]),(⟨1,2,3⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨1,2,4⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨1,3,0⟩,[0,-294912,9814016,-132628480,957874176,-3941826560,8101675008,2296856576,-63049957376,181021343744,-260831363072,210311233536,-238476984320,667196424192,-1040009707520,603119534080]),(⟨1,3,1⟩,[0,0,524288,-12713984,125960192,-664403968,1955201024,-2659450880,-1197211648,8723890176,-4420009984,-16395141120,-12212109312,143212281856,-165848940544]),(⟨1,3,2⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨1,3,3⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨1,4,0⟩,[0,0,524288,-12713984,125960192,-664403968,1955201024,-2659450880,-1197211648,8723890176,-4420009984,-16395141120,-12212109312,143212281856,-165848940544]),(⟨1,4,2⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨2,0,0⟩,[32768,-1015808,12632064,-76283904,155844608,910114816,-8104198144,28336029696,-45521764352,-18049286144,248690786304,-539803189248,591309832192,-492642713600,1046343794688,-2430460919808,2884513857536,-1342922964992]),(⟨2,0,1⟩,[0,-196608,5144576,-53051392,257753088,-365002752,-2446917632,15693905920,-43137925120,66303426560,-64694222848,93111353344,-227667607552,257784446976,232328658944,-909300137984,717471842304]),(⟨2,0,2⟩,[-32768,1048576,-13500416,88637440,-294944768,248545280,1838022656,-8293449728,17153032192,-19721551872,8814460928,8661270528,-9331376128,-26552664064,93520265216,-103161856000]),(⟨2,0,3⟩,[32768,-786432,7995392,-50167808,245268480,-978812928,2792554496,-4949475328,5560172544,-8067678208,16083058688,-15671984128,11169398784,-17844502528,967507968]),(⟨2,0,4⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨2,0,5⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨2,0,6⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨2,1,0⟩,[16384,-868352,16728064,-163512320,895434752,-2581151744,1257979904,19504693248,-81492787200,168470003712,-210223775744,204830867456,-298431299584,426640818176,-66446311424,-732009463808,745289416704]),(⟨2,1,1⟩,[0,-65536,2097152,-27787264,199622656,-847970304,2108293120,-2543190016,-354680832,4800970752,-7338721280,24996216832,-93342269440,134582829056,54836461568,-202971152384]),(⟨2,1,3⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨2,1,4⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨2,2,0⟩,[-65536,2097152,-27000832,177274880,-589889536,498139136,3648782336,-16315318272,33022607360,-36798595072,18555863040,-807337984,21426405376,-63183192064,94453366784,-102381518848]),(⟨2,2,3⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨2,3,0⟩,[16384,-163840,-1343488,20873216,-36225024,-577372160,4101996544,-12826640384,23189962752,-27181875200,23331373056,-22050996224,47479898112,-59018641408,-4885020672]),(⟨2,3,1⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨2,3,2⟩,[-131072,4259840,-55377920,366149632,-1235156992,1231683584,5890244608,-24815206400,36265525248,3873767424,-102482116608,170384621568,-106071261184]),(⟨2,3,3⟩,[0,786432,-18481152,167116800,-713555968,1233125376,995360768,-7698382848,10969677824,1134821376,-18849857536,14926872576]),(⟨2,4,0⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨2,4,1⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨2,4,2⟩,[131072,-3407872,32374784,-124125184,23330816,1247805440,-3694395392,3431727104,4881776640,-19337576448,20248395776,-2947940352]),(⟨2,4,5⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,5,0⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨2,5,2⟩,[65536,-2097152,24182784,-117440512,127008768,975175680,-3995467776,5003804672,4534894592,-22754099200,22109552640]),(⟨2,5,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,6,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨3,0,0⟩,[32768,-1523712,28049408,-275529728,1593540608,-5343887360,7354712064,18687639552,-123580219392,313235095552,-453401903104,400893624320,-376412012544,813527220224,-1357277298688,981832450048,-103285260288]),(⟨3,0,1⟩,[0,-163840,5455872,-73121792,517373952,-2047672320,3825844224,2770714624,-34664939520,89049628672,-113063313408,76694142976,-121622593536,399803809792,-578371698688,290061434880]),(⟨3,0,2⟩,[16384,-425984,5013504,-39092224,233062400,-1030225920,3115876352,-6130565120,7995965440,-8686829568,9495347200,-5172264960,1059241984,-599982080,-13666910208]),(⟨3,0,3⟩,[0,-262144,6324224,-65044480,369917952,-1247313920,2494103552,-3168337920,5161418752,-13640990720,19988381696,-5548441600,-1394704384,-17987436544]),(⟨3,0,4⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨3,0,5⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨3,1,0⟩,[0,-294912,9814016,-132628480,957874176,-3941826560,8101675008,2296856576,-63049957376,181021343744,-260831363072,210311233536,-238476984320,667196424192,-1040009707520,603119534080]),(⟨3,1,1⟩,[0,0,524288,-12713984,125960192,-664403968,1955201024,-2659450880,-1197211648,8723890176,-4420009984,-16395141120,-12212109312,143212281856,-165848940544]),(⟨3,1,2⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨3,1,3⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨3,2,0⟩,[16384,-163840,-1343488,20873216,-36225024,-577372160,4101996544,-12826640384,23189962752,-27181875200,23331373056,-22050996224,47479898112,-59018641408,-4885020672]),(⟨3,2,1⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨3,2,2⟩,[-131072,4259840,-55377920,366149632,-1235156992,1231683584,5890244608,-24815206400,36265525248,3873767424,-102482116608,170384621568,-106071261184]),(⟨3,2,3⟩,[0,786432,-18481152,167116800,-713555968,1233125376,995360768,-7698382848,10969677824,1134821376,-18849857536,14926872576]),(⟨3,3,0⟩,[0,-131072,2359296,-20447232,131072000,-702414848,2973237248,-9459204096,21941452800,-34574565376,31201689600,-18427150336,52131004416,-83851608064]),(⟨3,3,1⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨3,3,2⟩,[0,786432,-18481152,167116800,-713555968,1233125376,995360768,-7698382848,10969677824,1134821376,-18849857536,14926872576]),(⟨3,4,0⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨3,5,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨4,0,0⟩,[-32768,819200,-5783552,-16203776,463306752,-2846359552,7858667520,-3724984320,-44258787328,153854312448,-245605122048,212106166272,-194555248640,516138795008,-908738740224,598986637312]),(⟨4,0,1⟩,[0,0,524288,-12713984,125960192,-664403968,1955201024,-2659450880,-1197211648,8723890176,-4420009984,-16395141120,-12212109312,143212281856,-165848940544]),(⟨4,0,2⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨4,0,3⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨4,1,0⟩,[0,0,524288,-12713984,125960192,-664403968,1955201024,-2659450880,-1197211648,8723890176,-4420009984,-16395141120,-12212109312,143212281856,-165848940544]),(⟨4,1,2⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨4,2,0⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨4,2,1⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨4,2,2⟩,[131072,-3407872,32374784,-124125184,23330816,1247805440,-3694395392,3431727104,4881776640,-19337576448,20248395776,-2947940352]),(⟨4,2,5⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,3,0⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨4,5,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨5,0,0⟩,[-16384,884736,-15695872,131006464,-550780928,854294528,2295562240,-14573240320,32823787520,-37609242624,21084340224,-23257743360,82731155456,-99592798208,2929360896]),(⟨5,0,2⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨5,0,3⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨5,2,0⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨5,2,2⟩,[65536,-2097152,24182784,-117440512,127008768,975175680,-3995467776,5003804672,4534894592,-22754099200,22109552640]),(⟨5,2,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨5,3,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨5,4,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨6,0,0⟩,[0,131072,-3964928,44597248,-238845952,544899072,479133696,-6290866176,16780034048,-20933574656,11213307904,-12878708736,53525708800,-65864171520]),(⟨6,0,2⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨6,2,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,0⟩,[128,-2368,16192,-48960,27712,296128,-1096256,1862976,-1545664,318080]),(⟨0,0,1⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨0,0,2⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨0,0,3⟩,[-64,1280,-6336,2560,43072,-131840,181440])]

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[-32768,1261568,-21774336,222871552,-1497399296,6802866176,-19968475136,27498463232,53731688448,-415745081344,1217161904128,-2220882575360,2797804748800,-2946671738880,4010448109568,-6578272813056,7920494313472,-5368998379520,1590880403456,-163182673920]),(⟨0,0,1⟩,[-16384,901120,-19693568,237780992,-1798193152,8917073920,-28253552640,45166968832,47055781888,-493320847360,1462234513408,-2571785420800,3043433725952,-3200900972544,5040350494720,-8744576630784,9882432372736,-5629064118272,942321336320]),(⟨0,0,2⟩,[65536,-2211840,31326208,-240353280,1035567104,-1906769920,-4278288384,37483511808,-107184390144,140653363200,14058192896,-333458800640,440209080320,-225246838784,589153206272,-2095343992832,2854733742080,-1353182953472]),(⟨0,0,3⟩,[32768,-1785856,35586048,-367902720,2220654592,-7831764992,12288393216,21323333632,-170470375424,456312242176,-690367299584,642128330752,-605711532032,1238784950272,-2069775253504,1552855121920,-218750844928]),(⟨0,0,4⟩,[-32768,819200,-5783552,-16203776,463306752,-2846359552,7858667520,-3724984320,-44258787328,153854312448,-245605122048,212106166272,-194555248640,516138795008,-908738740224,598986637312]),(⟨0,0,5⟩,[-16384,884736,-15695872,131006464,-550780928,854294528,2295562240,-14573240320,32823787520,-37609242624,21084340224,-23257743360,82731155456,-99592798208,2929360896]),(⟨0,0,6⟩,[0,131072,-3964928,44597248,-238845952,544899072,479133696,-6290866176,16780034048,-20933574656,11213307904,-12878708736,53525708800,-65864171520]),(⟨0,1,0⟩,[-16384,901120,-19693568,237780992,-1798193152,8917073920,-28253552640,45166968832,47055781888,-493320847360,1462234513408,-2571785420800,3043433725952,-3200900972544,5040350494720,-8744576630784,9882432372736,-5629064118272,942321336320]),(⟨0,1,1⟩,[0,262144,-9535488,148701184,-1318846464,7323484160,-25682411520,49643651072,-577044480,-301328203776,935002734592,-1515015831552,1531750776832,-1765282119680,4116864204800,-7627501207552,7452979036160,-2975109251072]),(⟨0,1,2⟩,[16384,-868352,16728064,-163512320,895434752,-2581151744,1257979904,19504693248,-81492787200,168470003712,-210223775744,204830867456,-298431299584,426640818176,-66446311424,-732009463808,745289416704]),(⟨0,1,3⟩,[0,-294912,9814016,-132628480,957874176,-3941826560,8101675008,2296856576,-63049957376,181021343744,-260831363072,210311233536,-238476984320,667196424192,-1040009707520,603119534080]),(⟨0,1,4⟩,[0,0,524288,-12713984,125960192,-664403968,1955201024,-2659450880,-1197211648,8723890176,-4420009984,-16395141120,-12212109312,143212281856,-165848940544]),(⟨0,2,0⟩,[65536,-2211840,31326208,-240353280,1035567104,-1906769920,-4278288384,37483511808,-107184390144,140653363200,14058192896,-333458800640,440209080320,-225246838784,589153206272,-2095343992832,2854733742080,-1353182953472]),(⟨0,2,1⟩,[16384,-868352,16728064,-163512320,895434752,-2581151744,1257979904,19504693248,-81492787200,168470003712,-210223775744,204830867456,-298431299584,426640818176,-66446311424,-732009463808,745289416704]),(⟨0,2,2⟩,[-65536,2097152,-27000832,177274880,-589889536,498139136,3648782336,-16315318272,33022607360,-36798595072,18555863040,-807337984,21426405376,-63183192064,94453366784,-102381518848]),(⟨0,2,3⟩,[16384,-163840,-1343488,20873216,-36225024,-577372160,4101996544,-12826640384,23189962752,-27181875200,23331373056,-22050996224,47479898112,-59018641408,-4885020672]),(⟨0,2,4⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨0,2,5⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨0,2,6⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨0,3,0⟩,[32768,-1785856,35586048,-367902720,2220654592,-7831764992,12288393216,21323333632,-170470375424,456312242176,-690367299584,642128330752,-605711532032,1238784950272,-2069775253504,1552855121920,-218750844928]),(⟨0,3,1⟩,[0,-294912,9814016,-132628480,957874176,-3941826560,8101675008,2296856576,-63049957376,181021343744,-260831363072,210311233536,-238476984320,667196424192,-1040009707520,603119534080]),(⟨0,3,2⟩,[16384,-163840,-1343488,20873216,-36225024,-577372160,4101996544,-12826640384,23189962752,-27181875200,23331373056,-22050996224,47479898112,-59018641408,-4885020672]),(⟨0,3,3⟩,[0,-131072,2359296,-20447232,131072000,-702414848,2973237248,-9459204096,21941452800,-34574565376,31201689600,-18427150336,52131004416,-83851608064]),(⟨0,3,4⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨0,3,5⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨0,4,0⟩,[-32768,819200,-5783552,-16203776,463306752,-2846359552,7858667520,-3724984320,-44258787328,153854312448,-245605122048,212106166272,-194555248640,516138795008,-908738740224,598986637312]),(⟨0,4,1⟩,[0,0,524288,-12713984,125960192,-664403968,1955201024,-2659450880,-1197211648,8723890176,-4420009984,-16395141120,-12212109312,143212281856,-165848940544]),(⟨0,4,2⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨0,4,3⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨0,5,0⟩,[-16384,884736,-15695872,131006464,-550780928,854294528,2295562240,-14573240320,32823787520,-37609242624,21084340224,-23257743360,82731155456,-99592798208,2929360896]),(⟨0,5,2⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨0,5,3⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨0,6,0⟩,[0,131072,-3964928,44597248,-238845952,544899072,479133696,-6290866176,16780034048,-20933574656,11213307904,-12878708736,53525708800,-65864171520]),(⟨0,6,2⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨1,0,0⟩,[-16384,901120,-19693568,237780992,-1798193152,8917073920,-28253552640,45166968832,47055781888,-493320847360,1462234513408,-2571785420800,3043433725952,-3200900972544,5040350494720,-8744576630784,9882432372736,-5629064118272,942321336320]),(⟨1,0,1⟩,[0,262144,-9535488,148701184,-1318846464,7323484160,-25682411520,49643651072,-577044480,-301328203776,935002734592,-1515015831552,1531750776832,-1765282119680,4116864204800,-7627501207552,7452979036160,-2975109251072]),(⟨1,0,2⟩,[16384,-868352,16728064,-163512320,895434752,-2581151744,1257979904,19504693248,-81492787200,168470003712,-210223775744,204830867456,-298431299584,426640818176,-66446311424,-732009463808,745289416704]),(⟨1,0,3⟩,[0,-294912,9814016,-132628480,957874176,-3941826560,8101675008,2296856576,-63049957376,181021343744,-260831363072,210311233536,-238476984320,667196424192,-1040009707520,603119534080]),(⟨1,0,4⟩,[0,0,524288,-12713984,125960192,-664403968,1955201024,-2659450880,-1197211648,8723890176,-4420009984,-16395141120,-12212109312,143212281856,-165848940544]),(⟨1,1,0⟩,[0,262144,-9535488,148701184,-1318846464,7323484160,-25682411520,49643651072,-577044480,-301328203776,935002734592,-1515015831552,1531750776832,-1765282119680,4116864204800,-7627501207552,7452979036160,-2975109251072]),(⟨1,1,1⟩,[0,0,-1179648,33226752,-398131200,2672689152,-10947919872,26863534080,-30535385088,-21580480512,100463935488,-943915008,-304227876864,-36016619520,1896987230208,-3573163819008,2266474807296]),(⟨1,1,2⟩,[0,-65536,2097152,-27787264,199622656,-847970304,2108293120,-2543190016,-354680832,4800970752,-7338721280,24996216832,-93342269440,134582829056,54836461568,-202971152384]),(⟨1,1,3⟩,[0,0,524288,-12713984,125960192,-664403968,1955201024,-2659450880,-1197211648,8723890176,-4420009984,-16395141120,-12212109312,143212281856,-165848940544]),(⟨1,2,0⟩,[16384,-868352,16728064,-163512320,895434752,-2581151744,1257979904,19504693248,-81492787200,168470003712,-210223775744,204830867456,-298431299584,426640818176,-66446311424,-732009463808,745289416704]),(⟨1,2,1⟩,[0,-65536,2097152,-27787264,199622656,-847970304,2108293120,-2543190016,-354680832,4800970752,-7338721280,24996216832,-93342269440,134582829056,54836461568,-202971152384]),(⟨1,2,3⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨1,2,4⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨1,3,0⟩,[0,-294912,9814016,-132628480,957874176,-3941826560,8101675008,2296856576,-63049957376,181021343744,-260831363072,210311233536,-238476984320,667196424192,-1040009707520,603119534080]),(⟨1,3,1⟩,[0,0,524288,-12713984,125960192,-664403968,1955201024,-2659450880,-1197211648,8723890176,-4420009984,-16395141120,-12212109312,143212281856,-165848940544]),(⟨1,3,2⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨1,3,3⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨1,4,0⟩,[0,0,524288,-12713984,125960192,-664403968,1955201024,-2659450880,-1197211648,8723890176,-4420009984,-16395141120,-12212109312,143212281856,-165848940544]),(⟨1,4,2⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨2,0,0⟩,[65536,-2211840,31326208,-240353280,1035567104,-1906769920,-4278288384,37483511808,-107184390144,140653363200,14058192896,-333458800640,440209080320,-225246838784,589153206272,-2095343992832,2854733742080,-1353182953472]),(⟨2,0,1⟩,[16384,-868352,16728064,-163512320,895434752,-2581151744,1257979904,19504693248,-81492787200,168470003712,-210223775744,204830867456,-298431299584,426640818176,-66446311424,-732009463808,745289416704]),(⟨2,0,2⟩,[-65536,2097152,-27000832,177274880,-589889536,498139136,3648782336,-16315318272,33022607360,-36798595072,18555863040,-807337984,21426405376,-63183192064,94453366784,-102381518848]),(⟨2,0,3⟩,[16384,-163840,-1343488,20873216,-36225024,-577372160,4101996544,-12826640384,23189962752,-27181875200,23331373056,-22050996224,47479898112,-59018641408,-4885020672]),(⟨2,0,4⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨2,0,5⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨2,0,6⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨2,1,0⟩,[16384,-868352,16728064,-163512320,895434752,-2581151744,1257979904,19504693248,-81492787200,168470003712,-210223775744,204830867456,-298431299584,426640818176,-66446311424,-732009463808,745289416704]),(⟨2,1,1⟩,[0,-65536,2097152,-27787264,199622656,-847970304,2108293120,-2543190016,-354680832,4800970752,-7338721280,24996216832,-93342269440,134582829056,54836461568,-202971152384]),(⟨2,1,3⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨2,1,4⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨2,2,0⟩,[-65536,2097152,-27000832,177274880,-589889536,498139136,3648782336,-16315318272,33022607360,-36798595072,18555863040,-807337984,21426405376,-63183192064,94453366784,-102381518848]),(⟨2,2,2⟩,[-131072,3997696,-49610752,317128704,-1024524288,655884288,7688028160,-31463178240,50612404224,-52101120,-150870753280,274222743552,-200074133504,38759956480]),(⟨2,2,3⟩,[-131072,4259840,-55377920,366149632,-1235156992,1231683584,5890244608,-24815206400,36265525248,3873767424,-102482116608,170384621568,-106071261184]),(⟨2,2,4⟩,[131072,-3407872,32374784,-124125184,23330816,1247805440,-3694395392,3431727104,4881776640,-19337576448,20248395776,-2947940352]),(⟨2,2,5⟩,[65536,-2097152,24182784,-117440512,127008768,975175680,-3995467776,5003804672,4534894592,-22754099200,22109552640]),(⟨2,3,0⟩,[16384,-163840,-1343488,20873216,-36225024,-577372160,4101996544,-12826640384,23189962752,-27181875200,23331373056,-22050996224,47479898112,-59018641408,-4885020672]),(⟨2,3,1⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨2,3,2⟩,[-131072,4259840,-55377920,366149632,-1235156992,1231683584,5890244608,-24815206400,36265525248,3873767424,-102482116608,170384621568,-106071261184]),(⟨2,3,3⟩,[0,786432,-18481152,167116800,-713555968,1233125376,995360768,-7698382848,10969677824,1134821376,-18849857536,14926872576]),(⟨2,4,0⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨2,4,1⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨2,4,2⟩,[131072,-3407872,32374784,-124125184,23330816,1247805440,-3694395392,3431727104,4881776640,-19337576448,20248395776,-2947940352]),(⟨2,4,5⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,5,0⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨2,5,2⟩,[65536,-2097152,24182784,-117440512,127008768,975175680,-3995467776,5003804672,4534894592,-22754099200,22109552640]),(⟨2,5,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,6,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨3,0,0⟩,[32768,-1785856,35586048,-367902720,2220654592,-7831764992,12288393216,21323333632,-170470375424,456312242176,-690367299584,642128330752,-605711532032,1238784950272,-2069775253504,1552855121920,-218750844928]),(⟨3,0,1⟩,[0,-294912,9814016,-132628480,957874176,-3941826560,8101675008,2296856576,-63049957376,181021343744,-260831363072,210311233536,-238476984320,667196424192,-1040009707520,603119534080]),(⟨3,0,2⟩,[16384,-163840,-1343488,20873216,-36225024,-577372160,4101996544,-12826640384,23189962752,-27181875200,23331373056,-22050996224,47479898112,-59018641408,-4885020672]),(⟨3,0,3⟩,[0,-131072,2359296,-20447232,131072000,-702414848,2973237248,-9459204096,21941452800,-34574565376,31201689600,-18427150336,52131004416,-83851608064]),(⟨3,0,4⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨3,0,5⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨3,1,0⟩,[0,-294912,9814016,-132628480,957874176,-3941826560,8101675008,2296856576,-63049957376,181021343744,-260831363072,210311233536,-238476984320,667196424192,-1040009707520,603119534080]),(⟨3,1,1⟩,[0,0,524288,-12713984,125960192,-664403968,1955201024,-2659450880,-1197211648,8723890176,-4420009984,-16395141120,-12212109312,143212281856,-165848940544]),(⟨3,1,2⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨3,1,3⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨3,2,0⟩,[16384,-163840,-1343488,20873216,-36225024,-577372160,4101996544,-12826640384,23189962752,-27181875200,23331373056,-22050996224,47479898112,-59018641408,-4885020672]),(⟨3,2,1⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨3,2,2⟩,[-131072,4259840,-55377920,366149632,-1235156992,1231683584,5890244608,-24815206400,36265525248,3873767424,-102482116608,170384621568,-106071261184]),(⟨3,2,3⟩,[0,786432,-18481152,167116800,-713555968,1233125376,995360768,-7698382848,10969677824,1134821376,-18849857536,14926872576]),(⟨3,3,0⟩,[0,-131072,2359296,-20447232,131072000,-702414848,2973237248,-9459204096,21941452800,-34574565376,31201689600,-18427150336,52131004416,-83851608064]),(⟨3,3,1⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨3,3,2⟩,[0,786432,-18481152,167116800,-713555968,1233125376,995360768,-7698382848,10969677824,1134821376,-18849857536,14926872576]),(⟨3,4,0⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨3,5,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨4,0,0⟩,[-32768,819200,-5783552,-16203776,463306752,-2846359552,7858667520,-3724984320,-44258787328,153854312448,-245605122048,212106166272,-194555248640,516138795008,-908738740224,598986637312]),(⟨4,0,1⟩,[0,0,524288,-12713984,125960192,-664403968,1955201024,-2659450880,-1197211648,8723890176,-4420009984,-16395141120,-12212109312,143212281856,-165848940544]),(⟨4,0,2⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨4,0,3⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨4,1,0⟩,[0,0,524288,-12713984,125960192,-664403968,1955201024,-2659450880,-1197211648,8723890176,-4420009984,-16395141120,-12212109312,143212281856,-165848940544]),(⟨4,1,2⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨4,2,0⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨4,2,1⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨4,2,2⟩,[131072,-3407872,32374784,-124125184,23330816,1247805440,-3694395392,3431727104,4881776640,-19337576448,20248395776,-2947940352]),(⟨4,2,5⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,3,0⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨4,5,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨5,0,0⟩,[-16384,884736,-15695872,131006464,-550780928,854294528,2295562240,-14573240320,32823787520,-37609242624,21084340224,-23257743360,82731155456,-99592798208,2929360896]),(⟨5,0,2⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨5,0,3⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨5,2,0⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨5,2,2⟩,[65536,-2097152,24182784,-117440512,127008768,975175680,-3995467776,5003804672,4534894592,-22754099200,22109552640]),(⟨5,2,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨5,3,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨5,4,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨6,0,0⟩,[0,131072,-3964928,44597248,-238845952,544899072,479133696,-6290866176,16780034048,-20933574656,11213307904,-12878708736,53525708800,-65864171520]),(⟨6,0,2⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨6,2,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856])]


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
    (Poly.add (Poly.scale (K.ofRat r730) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 7 13).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r729*r729 : ℚ)=r730 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 7 13 r729 r729 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 7=13 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 7 13).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C128

#print axioms Coulomb8.Columns.C128.sound
