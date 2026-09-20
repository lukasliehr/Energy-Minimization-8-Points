import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C106

def r0 : ℚ := { num := -32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 1007616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -10993664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 393216, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 782893056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -10258292736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 71289700352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -338079907840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 1192018755584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -3259994103808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 7056393453568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -12109484589056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 16191086624768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -16214008291328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 11325657710592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -4825597935616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 939244666880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -8935211008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -40960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 1474560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -20807680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 18317312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := 59334656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := -7340687360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := 65446068224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -345206161408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := 1292613574656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := -3675726643200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 8171018190848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -14250883645440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 19116062580736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -1107680755712, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 12490042425344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -662408724480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 10699325440, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -1622016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 10141696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 89243648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -1897545728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 2107572224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -68262887424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 208875880448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -425358229504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 489681141760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 116968701952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -1818267631616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 4031379980288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -4958246764544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 495897968640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -21839511552, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 98304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -180224, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 33013760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -74350592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -225181696, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 378191872, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -107237588992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 409975717888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -1139930071040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 2396170665984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := -3801138577408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := 4363814273024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -3298870231040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 1297299881984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := -8449802240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 24576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := 147456, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -105807872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 80117760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -161226752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -13710360576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 1781399552, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -314504724480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 785152352256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -1406897405952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 1752159518720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -11587289088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 10726645760, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -8192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 1507328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -10534912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := -50397184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 1186521088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -1152778240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := 31569838080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := -84041400320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := 161542496256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -217919062016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 185652953088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -9898229760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -362340352, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 507904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -4505600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -8437760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 395411456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -177635328, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 12865667072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := -37786320896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := 4810784768, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -18003574784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 126419353600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -9336799232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 999424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -21233664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 223313920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := -1258307584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 174800896, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 9273081856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -115936100352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 81825808384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -274625445888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 4832509952000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -9200636231680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 12912433119232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -1802905436160, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 7687188381696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -314865385472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 49152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -1515520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 2260992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -27803648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -839794688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := 9290915840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -52299268096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := 194773549056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := -518010421248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 991121580032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -1285886541824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := 909380927488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 84424081408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -110087823360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 10442604544, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -73728, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 21839872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -168280064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 440606720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 2255921152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -25352503296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 120743100416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -386881249280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 912471367680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -1575944241152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 1895857012736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -204034727936, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 10463633408, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := -2146304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := 30310400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := -240664576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := 1187217408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := -3920068608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := 9451929600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := -966295552, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 9449242624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 47854665728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -152078090240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := 200393670656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := -946307072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := 16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := -671744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 10567680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -85934080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 404783104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -1156349952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 1954316288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -1170243584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -4215324672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 15721742336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -3450093568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 17809408, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -81920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := 131072, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := -23445504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := 119799808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -299663360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 259522560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 449085440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -270270464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 3146366976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -196476928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -1753088, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 1081344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -13238272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 77725696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := -236388352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 374276096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -181534720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -1059454976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := 3711139840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := -31490048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -16384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 2686976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -15106048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -2719744, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 2364391424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -15172141056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 55462133760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -125859201024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 168587018240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -83165446144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -16709419008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 228867211264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -17397202944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := -377520128, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -90112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := 2424832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -19415040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := -30408704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := 208281600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -10658381824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := 41951068160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -104812773376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 170822361088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -164189372416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := 49059315712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 10995630080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := -1695932416, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := -1327104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := 12435456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -37371904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := -113147904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := 995328000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -1868988416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := -1504346112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := 1341407232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := -8325120000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -1101971456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 15515648, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := 32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -720896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 163840, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := 47972352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -561446912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := 2363359232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -3926851584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := -1562640384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := 2228584448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -3260874752, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 14974976, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := 1277952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -2260992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 49971200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := 495124480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -5592383488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := 26642546688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := -79893299200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 168329314304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := -248441634816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := 238676115456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := -17082646528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -1572864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 786432, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := -42467328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 328728576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -382992384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := -4718592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := 2162688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -26476544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 155451392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -472776704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := 748552192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := -363069440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := -2118909952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := 7422279680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -62980096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := 196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := -8060928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := 132513792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := -1202454528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 7060389888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -29942022144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 96843595776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := -227149873152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 297113812992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := 19477364736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := -1463637639168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := 2962744934400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := -425793355776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := 1582497792, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := -327680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 9437184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -112066560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := 740556800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := -186318848, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := 9310306304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := -16060252160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := 69011308544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := -145896767488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := 110237974528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 6104547328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -118816768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := -131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := 262144, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := -59113472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := 417595392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -1892941824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := 907542528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := -15330967552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := 17624989696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := 22132686848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -113664327680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 174800896000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := -921960448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -1343488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 21135360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -171868160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 809566208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -2312699904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 3908632576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -2340487168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := -8430649344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := 31443484672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := -6900187136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := 35618816, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := -524288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 12582912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := -6291456, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := 339738624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := 105906176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := -2629828608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := 3063939072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := 37748736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := 131072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := -8880128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := 19988480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 271450112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := -2588934144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 10381230080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -2967339008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 1325694976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := 53729689600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := -19513376768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := 2984837120, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := -78446592, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := 262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := -6815744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := 3932160, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := -295698432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := 447217664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := 911212544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := -4320657408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := 4762632192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 3608412160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -119013376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := -23707648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := 126091264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := -353140736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := 61341696, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := 502038528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := -3206807552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := 4678336512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := 124387328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := -6209536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := -1966080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := 5603328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := 145686528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := -221970432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := 6455033856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := -11469914112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := -1002307584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := 40815525888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := -10305798144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := 1006338048, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := -6881280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := 3047424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := 41680896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := -507969536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := 2193489920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := -3979804672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := -35389440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := 14068121600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := -3581739008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := 19431424, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := 503808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := -5496832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := 196608, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := 391446528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := -5129146368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := 35644850176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := -169039953920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := 596009377792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := -1629997051904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := 3528196726784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := -6054742294528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := 8095543312384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := -8107004145664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := 5662828855296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := -2412798967808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := 469622333440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := -4467605504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := -20480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 737280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := -10403840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := 9158656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := 29667328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := -3670343680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := 32723034112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := -172603080704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := 646306787328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := -1837863321600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := 4085509095424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := -7125441822720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := 9558031290368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := -553840377856, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := 6245021212672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := -331204362240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := 5349662720, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := -811008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := 5070848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := 44621824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := -948772864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := 1053786112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := -34131443712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := 104437940224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := -212679114752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := 244840570880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := 58484350976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := -909133815808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := 2015689990144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := -2479123382272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := 247948984320, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := -10919755776, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := -90112, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := 16506880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := -37175296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := -112590848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := 189095936, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := -53618794496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := 204987858944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := -569965035520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := 1198085332992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := -1900569288704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := 2181907136512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := -1649435115520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := 648649940992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := -4224901120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := -8192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := 12288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := 73728, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := -52903936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := 40058880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := -80613376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := -6855180288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := 890699776, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := -157252362240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := 392576176128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := -703448702976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := 876079759360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := -5793644544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := 5363322880, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := -4096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := 753664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r454 : ℚ := { num := -5267456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r455 : ℚ := { num := -25198592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r456 : ℚ := { num := 593260544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r457 : ℚ := { num := -576389120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r458 : ℚ := { num := 15784919040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r459 : ℚ := { num := -42020700160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r460 : ℚ := { num := 80771248128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r461 : ℚ := { num := -108959531008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r462 : ℚ := { num := 92826476544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r463 : ℚ := { num := -4949114880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r464 : ℚ := { num := -181170176, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r465 : ℚ := { num := 253952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r466 : ℚ := { num := -2252800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r467 : ℚ := { num := -4218880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r468 : ℚ := { num := 197705728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r469 : ℚ := { num := -88817664, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r470 : ℚ := { num := 6432833536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r471 : ℚ := { num := -18893160448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r472 : ℚ := { num := 2405392384, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r473 : ℚ := { num := -9001787392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r474 : ℚ := { num := 63209676800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r475 : ℚ := { num := -4668399616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r476 : ℚ := { num := 499712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r477 : ℚ := { num := -10616832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r478 : ℚ := { num := 111656960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r479 : ℚ := { num := -629153792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r480 : ℚ := { num := 87400448, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r481 : ℚ := { num := 4636540928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r482 : ℚ := { num := -57968050176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r483 : ℚ := { num := 40912904192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r484 : ℚ := { num := -137312722944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r485 : ℚ := { num := 2416254976000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r486 : ℚ := { num := -4600318115840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r487 : ℚ := { num := 6456216559616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r488 : ℚ := { num := -901452718080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r489 : ℚ := { num := 3843594190848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r490 : ℚ := { num := -157432692736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r491 : ℚ := { num := -757760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r492 : ℚ := { num := 1130496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r493 : ℚ := { num := -13901824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r494 : ℚ := { num := -419897344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r495 : ℚ := { num := 4645457920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r496 : ℚ := { num := -26149634048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r497 : ℚ := { num := 97386774528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r498 : ℚ := { num := -259005210624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r499 : ℚ := { num := 495560790016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r500 : ℚ := { num := -642943270912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r501 : ℚ := { num := 454690463744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r502 : ℚ := { num := 42212040704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r503 : ℚ := { num := -55043911680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r504 : ℚ := { num := 5221302272, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r505 : ℚ := { num := -36864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r506 : ℚ := { num := 10919936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r507 : ℚ := { num := -84140032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r508 : ℚ := { num := 220303360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r509 : ℚ := { num := 1127960576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r510 : ℚ := { num := -12676251648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r511 : ℚ := { num := 60371550208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r512 : ℚ := { num := -193440624640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r513 : ℚ := { num := 456235683840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r514 : ℚ := { num := -787972120576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r515 : ℚ := { num := 947928506368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r516 : ℚ := { num := -102017363968, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r517 : ℚ := { num := 5231816704, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r518 : ℚ := { num := -1073152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r519 : ℚ := { num := 15155200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r520 : ℚ := { num := -120332288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r521 : ℚ := { num := 593608704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r522 : ℚ := { num := -1960034304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r523 : ℚ := { num := 4725964800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r524 : ℚ := { num := -483147776, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r525 : ℚ := { num := 4724621312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r526 : ℚ := { num := 23927332864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r527 : ℚ := { num := -76039045120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r528 : ℚ := { num := 100196835328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r529 : ℚ := { num := -473153536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r530 : ℚ := { num := 8192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r531 : ℚ := { num := -335872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r532 : ℚ := { num := 5283840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r533 : ℚ := { num := -42967040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r534 : ℚ := { num := 202391552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r535 : ℚ := { num := -578174976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r536 : ℚ := { num := 977158144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r537 : ℚ := { num := -585121792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r538 : ℚ := { num := -2107662336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r539 : ℚ := { num := 7860871168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r540 : ℚ := { num := -1725046784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r541 : ℚ := { num := 8904704, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r542 : ℚ := { num := 65536, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r543 : ℚ := { num := -11722752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r544 : ℚ := { num := 59899904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r545 : ℚ := { num := -149831680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r546 : ℚ := { num := 129761280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r547 : ℚ := { num := 224542720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r548 : ℚ := { num := -135135232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r549 : ℚ := { num := 1573183488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r550 : ℚ := { num := -98238464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r551 : ℚ := { num := -876544, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r552 : ℚ := { num := 540672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r553 : ℚ := { num := -6619136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r554 : ℚ := { num := 38862848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r555 : ℚ := { num := -118194176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r556 : ℚ := { num := 187138048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r557 : ℚ := { num := -90767360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r558 : ℚ := { num := -529727488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r559 : ℚ := { num := 1855569920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r560 : ℚ := { num := -15745024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r561 : ℚ := { num := 1343488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r562 : ℚ := { num := -7553024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r563 : ℚ := { num := -1359872, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r564 : ℚ := { num := 1182195712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r565 : ℚ := { num := -7586070528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r566 : ℚ := { num := 27731066880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r567 : ℚ := { num := -62929600512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r568 : ℚ := { num := 84293509120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r569 : ℚ := { num := -41582723072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r570 : ℚ := { num := -8354709504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r571 : ℚ := { num := 114433605632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r572 : ℚ := { num := -8698601472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r573 : ℚ := { num := -188760064, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r574 : ℚ := { num := -45056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r575 : ℚ := { num := 1212416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r576 : ℚ := { num := -9707520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r577 : ℚ := { num := -15204352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r578 : ℚ := { num := 104140800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r579 : ℚ := { num := -5329190912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r580 : ℚ := { num := 20975534080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r581 : ℚ := { num := -52406386688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r582 : ℚ := { num := 85411180544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r583 : ℚ := { num := -82094686208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r584 : ℚ := { num := 24529657856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r585 : ℚ := { num := 5497815040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r586 : ℚ := { num := -847966208, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r587 : ℚ := { num := -663552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r588 : ℚ := { num := 6217728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r589 : ℚ := { num := -18685952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r590 : ℚ := { num := -56573952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r591 : ℚ := { num := 497664000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r592 : ℚ := { num := -934494208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r593 : ℚ := { num := -752173056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r594 : ℚ := { num := 670703616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r595 : ℚ := { num := -4162560000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r596 : ℚ := { num := -550985728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r597 : ℚ := { num := 7757824, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r598 : ℚ := { num := -360448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r599 : ℚ := { num := 81920, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r600 : ℚ := { num := 23986176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r601 : ℚ := { num := -280723456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r602 : ℚ := { num := 1181679616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r603 : ℚ := { num := -1963425792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r604 : ℚ := { num := -781320192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r605 : ℚ := { num := 1114292224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r606 : ℚ := { num := -1630437376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r607 : ℚ := { num := 7487488, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r608 : ℚ := { num := 638976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r609 : ℚ := { num := -1130496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r610 : ℚ := { num := 24985600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r611 : ℚ := { num := 247562240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r612 : ℚ := { num := -2796191744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r613 : ℚ := { num := 13321273344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r614 : ℚ := { num := -39946649600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r615 : ℚ := { num := 84164657152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r616 : ℚ := { num := -124220817408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r617 : ℚ := { num := 119338057728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r618 : ℚ := { num := -8541323264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r619 : ℚ := { num := -786432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r620 : ℚ := { num := 393216, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r621 : ℚ := { num := 164364288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r622 : ℚ := { num := -191496192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r623 : ℚ := { num := -2359296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r624 : ℚ := { num := -4030464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r625 : ℚ := { num := 66256896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r626 : ℚ := { num := -601227264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r627 : ℚ := { num := 3530194944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r628 : ℚ := { num := -14971011072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r629 : ℚ := { num := 48421797888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r630 : ℚ := { num := -113574936576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r631 : ℚ := { num := 148556906496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r632 : ℚ := { num := 9738682368, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r633 : ℚ := { num := -731818819584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r634 : ℚ := { num := 1481372467200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r635 : ℚ := { num := -212896677888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r636 : ℚ := { num := 791248896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r637 : ℚ := { num := -163840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r638 : ℚ := { num := 4718592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r639 : ℚ := { num := -56033280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r640 : ℚ := { num := 370278400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r641 : ℚ := { num := -93159424, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r642 : ℚ := { num := 4655153152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r643 : ℚ := { num := -8030126080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r644 : ℚ := { num := 34505654272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r645 : ℚ := { num := -72948383744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r646 : ℚ := { num := 55118987264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r647 : ℚ := { num := 3052273664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r648 : ℚ := { num := -59408384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r649 : ℚ := { num := -29556736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r650 : ℚ := { num := 208797696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r651 : ℚ := { num := -946470912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r652 : ℚ := { num := 453771264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r653 : ℚ := { num := -7665483776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r654 : ℚ := { num := 8812494848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r655 : ℚ := { num := 11066343424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r656 : ℚ := { num := -56832163840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r657 : ℚ := { num := 87400448000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r658 : ℚ := { num := -460980224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r659 : ℚ := { num := -262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r660 : ℚ := { num := 6291456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r661 : ℚ := { num := -3145728, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r662 : ℚ := { num := 169869312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r663 : ℚ := { num := 52953088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r664 : ℚ := { num := -1314914304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r665 : ℚ := { num := 1531969536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r666 : ℚ := { num := 18874368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r667 : ℚ := { num := 65536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r668 : ℚ := { num := -4440064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r669 : ℚ := { num := 9994240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r670 : ℚ := { num := 135725056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r671 : ℚ := { num := -1294467072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r672 : ℚ := { num := 5190615040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r673 : ℚ := { num := -1483669504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r674 : ℚ := { num := 662847488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r675 : ℚ := { num := 26864844800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r676 : ℚ := { num := -9756688384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r677 : ℚ := { num := 1492418560, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r678 : ℚ := { num := -39223296, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r679 : ℚ := { num := 131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r680 : ℚ := { num := -3407872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r681 : ℚ := { num := 1966080, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r682 : ℚ := { num := -147849216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r683 : ℚ := { num := 223608832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r684 : ℚ := { num := 455606272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r685 : ℚ := { num := -2160328704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r686 : ℚ := { num := 2381316096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r687 : ℚ := { num := 1804206080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r688 : ℚ := { num := -59506688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r689 : ℚ := { num := -11853824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r690 : ℚ := { num := 63045632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r691 : ℚ := { num := -176570368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r692 : ℚ := { num := 30670848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r693 : ℚ := { num := 251019264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r694 : ℚ := { num := -1603403776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r695 : ℚ := { num := 2339168256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r696 : ℚ := { num := 62193664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r697 : ℚ := { num := -3104768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r698 : ℚ := { num := -983040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r699 : ℚ := { num := 2801664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r700 : ℚ := { num := 72843264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r701 : ℚ := { num := -110985216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r702 : ℚ := { num := 3227516928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r703 : ℚ := { num := -5734957056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r704 : ℚ := { num := -501153792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r705 : ℚ := { num := 20407762944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r706 : ℚ := { num := -5152899072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r707 : ℚ := { num := 503169024, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r708 : ℚ := { num := -3440640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r709 : ℚ := { num := 1523712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r710 : ℚ := { num := 20840448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r711 : ℚ := { num := -253984768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r712 : ℚ := { num := 1096744960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r713 : ℚ := { num := -1989902336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r714 : ℚ := { num := -17694720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r715 : ℚ := { num := 7034060800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r716 : ℚ := { num := -1790869504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r717 : ℚ := { num := 9715712, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r718 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r719 : ℚ := { num := 1, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17],[r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34],[r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50],[r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63,r64,r65],[r66,r67,r68,r69,r70,r71,r72,r73,r74,r75,r76,r77,r78,r79],[r80,r81,r82,r83,r84,r85,r86,r87,r88,r89,r90,r91,r92],[r66,r93,r94,r95,r96,r97,r98,r99,r100,r101,r102,r103],[],[],[],[],[],[],[r66,r104,r105,r106,r107,r108,r109,r110,r111,r112,r113,r114,r115,r116,r117,r118],[r119,r120,r121,r122,r123,r124,r125,r126,r127,r128,r129,r130,r131,r132,r133],[r67,r134,r135,r136,r137,r138,r139,r140,r141,r142,r143,r144,r145,r146],[r35,r147,r148,r149,r150,r151,r152,r153,r154,r155,r156,r157,r158],[r159,r160,r161,r162,r163,r164,r165,r166,r167,r168,r169,r170],[r171,r172,r173,r174,r175,r176,r177,r178,r179,r180,r181],[r0,r182,r183,r184,r185,r186,r187,r188,r189,r190],[],[],[],[],[r191,r192,r193,r194,r195,r196,r197,r198,r199,r200,r201,r202,r203,r204],[r205,r206,r207,r208,r209,r210,r211,r212,r213,r214,r215,r216,r217],[r119,r218,r219,r220,r221,r222,r223,r224,r225,r226,r227,r228],[r229,r230,r231,r232,r233,r234,r235,r236,r237,r238,r239],[],[],[],[],[],[r0,r240,r241,r242,r243,r244,r245,r246,r247,r248,r249,r250],[r171,r172,r173,r174,r175,r176,r177,r178,r179,r180,r181],[],[r35,r251,r252,r253,r183,r254,r255,r256,65536],[],[],[],[r257,r258,r259,r260,r261,r262,r263,r264,r265,r266],[],[],[],[],[],[],[],[],[0,r267,r268,r269,r270,r271,r272,r273,r274,r275,r276,r277,r278,r279,r280],[0,r281,r282,r283,r284,r285,r286,r287,r253,r288,r289,r290,r291,r292],[0,r293,r294,r295,r296,r297,r298,r299,r300,r301,r302,r303,r304],[r229,r305,r306,r307,r308,r309,r310,r311,r312,r313,r314,r315],[0,0,r316,r317,r318,r319,r320,r321,r322,r323,-524288],[],[],[],[],[],[r0,r324,r325,r326,r327,r328,r329,r330,r331,r332,r333,r334,r335],[0,r336,r337,r338,r339,r340,r341,r342,r343,r344,r345,786432],[r171,r172,r346,r347,r348,r349,r350,r351,r352,r353,r354],[],[r35,r251,r252,r253,r183,r254,r255,r256,65536],[],[],[],[],[r0,r182,r183,r184,r185,r186,r187,r188,r189,r190],[],[],[],[],[],[],[],[],[],[],[r51,r355,r356,r357,r358,r359,r360,r361,r362,r363,r364,r365],[r229,r230,r366,r367,r368,r369,r370,r371,r372,r373,r374],[],[],[],[],[],[],[r35,r251,r252,r253,r183,r254,r255,r256,65536],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[r66,r375,r376,r377,r378,r379,r380,r381,r382,r383,r384,r385,r386,r387,r388,r389,r390,r391]),(⟨0,0,1⟩,[r392,r393,r394,r395,r396,r397,r398,r399,r400,r401,r402,r403,r404,r405,r406,r407,r408]),(⟨0,0,2⟩,[r229,r409,r410,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423]),(⟨0,0,3⟩,[r119,r424,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434,r435,r436,r437]),(⟨0,0,4⟩,[r438,r439,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451]),(⟨0,0,5⟩,[r452,r453,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464]),(⟨0,0,6⟩,[r438,r465,r466,r467,r468,r469,r470,r471,r472,r473,r474,r475]),(⟨0,1,0⟩,[r392,r393,r394,r395,r396,r397,r398,r399,r400,r401,r402,r403,r404,r405,r406,r407,r408]),(⟨0,1,1⟩,[r438,r476,r477,r478,r479,r480,r481,r482,r483,r484,r485,r486,r487,r488,r489,r490]),(⟨0,1,2⟩,[r67,r491,r492,r493,r494,r495,r496,r497,r498,r499,r500,r501,r502,r503,r504]),(⟨0,1,3⟩,[r439,r505,r506,r507,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517]),(⟨0,1,4⟩,[r229,r518,r519,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529]),(⟨0,1,5⟩,[r530,r531,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541]),(⟨0,1,6⟩,[r18,r542,r543,r544,r545,r546,r547,r548,r549,r550,r551]),(⟨0,1,7⟩,[r66,r552,r553,r554,r555,r556,r557,r558,r559,r560]),(⟨0,2,0⟩,[r229,r409,r410,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423]),(⟨0,2,1⟩,[r67,r491,r492,r493,r494,r495,r496,r497,r498,r499,r500,r501,r502,r503,r504]),(⟨0,2,2⟩,[r80,r561,r562,r563,r564,r565,r566,r567,r568,r569,r570,r571,r572,r573]),(⟨0,2,3⟩,[r574,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584,r585,r586]),(⟨0,2,4⟩,[r67,r587,r588,r589,r590,r591,r592,r593,r594,r595,r596,r597]),(⟨0,2,5⟩,[r159,r598,r599,r600,r601,r602,r603,r604,r605,r606,r607]),(⟨0,3,0⟩,[r119,r424,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434,r435,r436,r437]),(⟨0,3,1⟩,[r439,r505,r506,r507,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517]),(⟨0,3,2⟩,[r574,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584,r585,r586]),(⟨0,3,3⟩,[r66,r608,r609,r610,r611,r612,r613,r614,r615,r616,r617,r618]),(⟨0,3,4⟩,[r18,r542,r543,r544,r545,r546,r547,r548,r549,r550,r551]),(⟨0,3,6⟩,[r229,r619,r620,r105,r553,r621,r622,r623,32768]),(⟨0,4,0⟩,[r438,r439,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451]),(⟨0,4,1⟩,[r229,r518,r519,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529]),(⟨0,4,2⟩,[r67,r587,r588,r589,r590,r591,r592,r593,r594,r595,r596,r597]),(⟨0,4,3⟩,[r18,r542,r543,r544,r545,r546,r547,r548,r549,r550,r551]),(⟨0,4,4⟩,[r0,r182,r183,r184,r185,r186,r187,r188,r189,r190]),(⟨0,5,0⟩,[r452,r453,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464]),(⟨0,5,1⟩,[r530,r531,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541]),(⟨0,5,2⟩,[r159,r598,r599,r600,r601,r602,r603,r604,r605,r606,r607]),(⟨0,6,0⟩,[r438,r465,r466,r467,r468,r469,r470,r471,r472,r473,r474,r475]),(⟨0,6,1⟩,[r18,r542,r543,r544,r545,r546,r547,r548,r549,r550,r551]),(⟨0,6,3⟩,[r229,r619,r620,r105,r553,r621,r622,r623,32768]),(⟨0,7,1⟩,[r66,r552,r553,r554,r555,r556,r557,r558,r559,r560]),(⟨1,0,0⟩,[r392,r393,r394,r395,r396,r397,r398,r399,r400,r401,r402,r403,r404,r405,r406,r407,r408]),(⟨1,0,1⟩,[r438,r476,r477,r478,r479,r480,r481,r482,r483,r484,r485,r486,r487,r488,r489,r490]),(⟨1,0,2⟩,[r67,r491,r492,r493,r494,r495,r496,r497,r498,r499,r500,r501,r502,r503,r504]),(⟨1,0,3⟩,[r439,r505,r506,r507,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517]),(⟨1,0,4⟩,[r229,r518,r519,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529]),(⟨1,0,5⟩,[r530,r531,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541]),(⟨1,0,6⟩,[r18,r542,r543,r544,r545,r546,r547,r548,r549,r550,r551]),(⟨1,0,7⟩,[r66,r552,r553,r554,r555,r556,r557,r558,r559,r560]),(⟨1,1,0⟩,[r438,r476,r477,r478,r479,r480,r481,r482,r483,r484,r485,r486,r487,r488,r489,r490]),(⟨1,1,1⟩,[0,r51,r624,r625,r626,r627,r628,r629,r630,r631,r632,r633,r634,r635,r636]),(⟨1,1,2⟩,[0,r637,r638,r639,r640,r641,r642,r643,r105,r644,r645,r646,r647,r648]),(⟨1,1,3⟩,[0,r257,r172,r649,r650,r651,r652,r653,r654,r655,r656,r657,r658]),(⟨1,1,4⟩,[r159,r160,r161,r162,r163,r164,r165,r166,r167,r168,r169,r170]),(⟨1,1,5⟩,[0,0,r659,r660,r661,r662,r663,r664,r665,r666,-262144]),(⟨1,2,0⟩,[r67,r491,r492,r493,r494,r495,r496,r497,r498,r499,r500,r501,r502,r503,r504]),(⟨1,2,1⟩,[0,r637,r638,r639,r640,r641,r642,r643,r105,r644,r645,r646,r647,r648]),(⟨1,2,2⟩,[r66,r667,r668,r669,r670,r671,r672,r673,r674,r675,r676,r677,r678]),(⟨1,2,3⟩,[0,r679,r680,r681,r682,r683,r684,r685,r686,r687,r688,393216]),(⟨1,2,4⟩,[r18,r542,r689,r690,r691,r692,r693,r694,r695,r696,r697]),(⟨1,2,6⟩,[r229,r619,r620,r105,r553,r621,r622,r623,32768]),(⟨1,3,0⟩,[r439,r505,r506,r507,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517]),(⟨1,3,1⟩,[0,r257,r172,r649,r650,r651,r652,r653,r654,r655,r656,r657,r658]),(⟨1,3,2⟩,[0,r679,r680,r681,r682,r683,r684,r685,r686,r687,r688,393216]),(⟨1,3,4⟩,[r66,r552,r553,r554,r555,r556,r557,r558,r559,r560]),(⟨1,4,0⟩,[r229,r518,r519,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529]),(⟨1,4,1⟩,[r159,r160,r161,r162,r163,r164,r165,r166,r167,r168,r169,r170]),(⟨1,4,2⟩,[r18,r542,r689,r690,r691,r692,r693,r694,r695,r696,r697]),(⟨1,4,3⟩,[r66,r552,r553,r554,r555,r556,r557,r558,r559,r560]),(⟨1,5,0⟩,[r530,r531,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541]),(⟨1,5,1⟩,[0,0,r659,r660,r661,r662,r663,r664,r665,r666,-262144]),(⟨1,6,0⟩,[r18,r542,r543,r544,r545,r546,r547,r548,r549,r550,r551]),(⟨1,6,2⟩,[r229,r619,r620,r105,r553,r621,r622,r623,32768]),(⟨1,7,0⟩,[r66,r552,r553,r554,r555,r556,r557,r558,r559,r560]),(⟨2,0,0⟩,[r229,r409,r410,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423]),(⟨2,0,1⟩,[r67,r491,r492,r493,r494,r495,r496,r497,r498,r499,r500,r501,r502,r503,r504]),(⟨2,0,2⟩,[r80,r561,r562,r563,r564,r565,r566,r567,r568,r569,r570,r571,r572,r573]),(⟨2,0,3⟩,[r574,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584,r585,r586]),(⟨2,0,4⟩,[r67,r587,r588,r589,r590,r591,r592,r593,r594,r595,r596,r597]),(⟨2,0,5⟩,[r159,r598,r599,r600,r601,r602,r603,r604,r605,r606,r607]),(⟨2,1,0⟩,[r67,r491,r492,r493,r494,r495,r496,r497,r498,r499,r500,r501,r502,r503,r504]),(⟨2,1,1⟩,[0,r637,r638,r639,r640,r641,r642,r643,r105,r644,r645,r646,r647,r648]),(⟨2,1,2⟩,[r66,r667,r668,r669,r670,r671,r672,r673,r674,r675,r676,r677,r678]),(⟨2,1,3⟩,[0,r679,r680,r681,r682,r683,r684,r685,r686,r687,r688,393216]),(⟨2,1,4⟩,[r18,r542,r689,r690,r691,r692,r693,r694,r695,r696,r697]),(⟨2,1,6⟩,[r229,r619,r620,r105,r553,r621,r622,r623,32768]),(⟨2,2,0⟩,[r80,r561,r562,r563,r564,r565,r566,r567,r568,r569,r570,r571,r572,r573]),(⟨2,2,1⟩,[r66,r667,r668,r669,r670,r671,r672,r673,r674,r675,r676,r677,r678]),(⟨2,2,2⟩,[r119,r698,r699,r700,r701,r702,r703,r704,r705,r706,r707,r708]),(⟨2,2,3⟩,[r159,r598,r709,r710,r711,r712,r713,r714,r715,r716,r717]),(⟨2,3,0⟩,[r574,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584,r585,r586]),(⟨2,3,1⟩,[0,r679,r680,r681,r682,r683,r684,r685,r686,r687,r688,393216]),(⟨2,3,2⟩,[r159,r598,r709,r710,r711,r712,r713,r714,r715,r716,r717]),(⟨2,3,4⟩,[r229,r619,r620,r105,r553,r621,r622,r623,32768]),(⟨2,4,0⟩,[r67,r587,r588,r589,r590,r591,r592,r593,r594,r595,r596,r597]),(⟨2,4,1⟩,[r18,r542,r689,r690,r691,r692,r693,r694,r695,r696,r697]),(⟨2,4,3⟩,[r229,r619,r620,r105,r553,r621,r622,r623,32768]),(⟨2,5,0⟩,[r159,r598,r599,r600,r601,r602,r603,r604,r605,r606,r607]),(⟨2,6,1⟩,[r229,r619,r620,r105,r553,r621,r622,r623,32768]),(⟨3,0,0⟩,[r119,r424,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434,r435,r436,r437]),(⟨3,0,1⟩,[r439,r505,r506,r507,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517]),(⟨3,0,2⟩,[r574,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584,r585,r586]),(⟨3,0,3⟩,[r66,r608,r609,r610,r611,r612,r613,r614,r615,r616,r617,r618]),(⟨3,0,4⟩,[r18,r542,r543,r544,r545,r546,r547,r548,r549,r550,r551]),(⟨3,0,6⟩,[r229,r619,r620,r105,r553,r621,r622,r623,32768]),(⟨3,1,0⟩,[r439,r505,r506,r507,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517]),(⟨3,1,1⟩,[0,r257,r172,r649,r650,r651,r652,r653,r654,r655,r656,r657,r658]),(⟨3,1,2⟩,[0,r679,r680,r681,r682,r683,r684,r685,r686,r687,r688,393216]),(⟨3,1,4⟩,[r66,r552,r553,r554,r555,r556,r557,r558,r559,r560]),(⟨3,2,0⟩,[r574,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584,r585,r586]),(⟨3,2,1⟩,[0,r679,r680,r681,r682,r683,r684,r685,r686,r687,r688,393216]),(⟨3,2,2⟩,[r159,r598,r709,r710,r711,r712,r713,r714,r715,r716,r717]),(⟨3,2,4⟩,[r229,r619,r620,r105,r553,r621,r622,r623,32768]),(⟨3,3,0⟩,[r66,r608,r609,r610,r611,r612,r613,r614,r615,r616,r617,r618]),(⟨3,4,0⟩,[r18,r542,r543,r544,r545,r546,r547,r548,r549,r550,r551]),(⟨3,4,1⟩,[r66,r552,r553,r554,r555,r556,r557,r558,r559,r560]),(⟨3,4,2⟩,[r229,r619,r620,r105,r553,r621,r622,r623,32768]),(⟨3,6,0⟩,[r229,r619,r620,r105,r553,r621,r622,r623,32768]),(⟨4,0,0⟩,[r438,r439,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451]),(⟨4,0,1⟩,[r229,r518,r519,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529]),(⟨4,0,2⟩,[r67,r587,r588,r589,r590,r591,r592,r593,r594,r595,r596,r597]),(⟨4,0,3⟩,[r18,r542,r543,r544,r545,r546,r547,r548,r549,r550,r551]),(⟨4,0,4⟩,[r0,r182,r183,r184,r185,r186,r187,r188,r189,r190]),(⟨4,1,0⟩,[r229,r518,r519,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529]),(⟨4,1,1⟩,[r159,r160,r161,r162,r163,r164,r165,r166,r167,r168,r169,r170]),(⟨4,1,2⟩,[r18,r542,r689,r690,r691,r692,r693,r694,r695,r696,r697]),(⟨4,1,3⟩,[r66,r552,r553,r554,r555,r556,r557,r558,r559,r560]),(⟨4,2,0⟩,[r67,r587,r588,r589,r590,r591,r592,r593,r594,r595,r596,r597]),(⟨4,2,1⟩,[r18,r542,r689,r690,r691,r692,r693,r694,r695,r696,r697]),(⟨4,2,3⟩,[r229,r619,r620,r105,r553,r621,r622,r623,32768]),(⟨4,3,0⟩,[r18,r542,r543,r544,r545,r546,r547,r548,r549,r550,r551]),(⟨4,3,1⟩,[r66,r552,r553,r554,r555,r556,r557,r558,r559,r560]),(⟨4,3,2⟩,[r229,r619,r620,r105,r553,r621,r622,r623,32768]),(⟨4,4,0⟩,[r0,r182,r183,r184,r185,r186,r187,r188,r189,r190]),(⟨5,0,0⟩,[r452,r453,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464]),(⟨5,0,1⟩,[r530,r531,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541]),(⟨5,0,2⟩,[r159,r598,r599,r600,r601,r602,r603,r604,r605,r606,r607]),(⟨5,1,0⟩,[r530,r531,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541]),(⟨5,1,1⟩,[0,0,r659,r660,r661,r662,r663,r664,r665,r666,-262144]),(⟨5,2,0⟩,[r159,r598,r599,r600,r601,r602,r603,r604,r605,r606,r607]),(⟨6,0,0⟩,[r438,r465,r466,r467,r468,r469,r470,r471,r472,r473,r474,r475]),(⟨6,0,1⟩,[r18,r542,r543,r544,r545,r546,r547,r548,r549,r550,r551]),(⟨6,0,3⟩,[r229,r619,r620,r105,r553,r621,r622,r623,32768]),(⟨6,1,0⟩,[r18,r542,r543,r544,r545,r546,r547,r548,r549,r550,r551]),(⟨6,1,2⟩,[r229,r619,r620,r105,r553,r621,r622,r623,32768]),(⟨6,2,1⟩,[r229,r619,r620,r105,r553,r621,r622,r623,32768]),(⟨6,3,0⟩,[r229,r619,r620,r105,r553,r621,r622,r623,32768]),(⟨7,0,1⟩,[r66,r552,r553,r554,r555,r556,r557,r558,r559,r560]),(⟨7,1,0⟩,[r66,r552,r553,r554,r555,r556,r557,r558,r559,r560])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[64,-768,-1856,71168,-470336,1581440,-3104960,3581696,-2132736,328832]),(⟨0,0,1⟩,[64,-1024,3136,27008,-255680,943360,-1884224,2076032,-1072512]),(⟨0,0,2⟩,[-64,512,4416,-54912,194112,-323840,260288,-31360]),(⟨0,0,3⟩,[-64,640,3648,-54528,197696,-331136,265664]),(⟨0,1,0⟩,[64,-1024,3136,27008,-255680,943360,-1884224,2076032,-1072512]),(⟨0,1,1⟩,[0,-512,7168,-29184,30720,51712,-177152,182784]),(⟨0,1,4⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[-64,512,4416,-54912,194112,-323840,260288,-31360]),(⟨0,3,0⟩,[-64,640,3648,-54528,197696,-331136,265664]),(⟨0,4,1⟩,[-128,1536,-3840,-4608,15232]),(⟨1,0,0⟩,[64,-1024,3136,27008,-255680,943360,-1884224,2076032,-1072512]),(⟨1,0,1⟩,[0,-512,7168,-29184,30720,51712,-177152,182784]),(⟨1,0,4⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[0,-512,7168,-29184,30720,51712,-177152,182784]),(⟨1,4,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[-64,512,4416,-54912,194112,-323840,260288,-31360]),(⟨3,0,0⟩,[-64,640,3648,-54528,197696,-331136,265664]),(⟨4,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨4,1,0⟩,[-128,1536,-3840,-4608,15232])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[-256,4800,-35712,145856,-387968,744000,-1039488,811328,-95104]),(⟨0,0,1⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨0,0,2⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨0,0,3⟩,[128,-2688,15616,-40192,84608,-123008]),(⟨0,1,0⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨0,1,1⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨0,2,0⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨0,2,2⟩,[-256,3072,-7680,-9216,30464]),(⟨0,3,0⟩,[128,-2688,15616,-40192,84608,-123008]),(⟨1,0,0⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨1,0,1⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨1,1,0⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨2,0,0⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨2,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨2,2,0⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[128,-2688,15616,-40192,84608,-123008])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 5 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r718) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 6 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r718) sourceRight))).isZero := by decide +kernel

noncomputable def partial19 : Poly := []

theorem partial_sound19 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 19)
      sourceRight).eval u v t=partial19.eval u v t := by rfl

noncomputable def chunk16 : Poly := [(⟨3,0,0⟩,[-64,640,3648,-54528,197696,-331136,265664]),(⟨4,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨4,1,0⟩,[-128,1536,-3840,-4608,15232])]

noncomputable def partial16 : Poly := [(⟨3,0,0⟩,[16384,-471040,4423680,-720896,-324444160,3217182720,-17543438336,65087897600,-178320834560,373884743680,-599523966976,707448045568,-563616129024,247032999936,-25265709056]),(⟨3,0,1⟩,[4096,-159744,2048000,-5619712,-112930816,1435062272,-8684765184,34375139328,-99052244992,216713211904,-358424788992,427845926912,-332725456896,129371992064]),(⟨3,0,2⟩,[-20480,516096,-3457024,-16867328,377843712,-2487697408,9332195328,-23268999168,40428474368,-46731534336,29708697600,27009024,-12734869504]),(⟨3,0,3⟩,[-8192,253952,-2252800,-4218880,197705728,-1509900288,6432833536,-18893160448,40891670528,-63012511744,63209676800,-32678797312]),(⟨3,1,0⟩,[4096,-159744,2048000,-5619712,-112930816,1435062272,-8684765184,34375139328,-99052244992,216713211904,-358424788992,427845926912,-332725456896,129371992064]),(⟨3,1,1⟩,[0,0,-65536,1441792,-6094848,-83361792,1015939072,-4386979840,7959609344,495452160,-28136243200,50144346112,-32372752384]),(⟨3,2,0⟩,[-20480,516096,-3457024,-16867328,377843712,-2487697408,9332195328,-23268999168,40428474368,-46731534336,29708697600,27009024,-12734869504]),(⟨3,2,2⟩,[16384,-360448,1523712,20840448,-253984768,1096744960,-1989902336,-123863040,7034060800,-12536086528,8093188096]),(⟨3,3,0⟩,[-8192,253952,-2252800,-4218880,197705728,-1509900288,6432833536,-18893160448,40891670528,-63012511744,63209676800,-32678797312]),(⟨4,0,0⟩,[4096,-159744,2048000,-5619712,-112930816,1435062272,-8684765184,34375139328,-99052244992,216713211904,-358424788992,427845926912,-332725456896,129371992064]),(⟨4,0,1⟩,[32768,-1007616,12861440,-89333760,378716160,-1096925184,2565505024,-4935008256,3871735808,13356441600,-47343124480,62940733440,-33821376512]),(⟨4,0,2⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨4,0,3⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨4,0,4⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨4,1,0⟩,[32768,-1007616,12861440,-89333760,378716160,-1096925184,2565505024,-4935008256,3871735808,13356441600,-47343124480,62940733440,-33821376512]),(⟨4,1,1⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨4,1,2⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨4,1,3⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨4,2,0⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨4,2,1⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨4,2,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,3,0⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨4,3,1⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨4,3,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,4,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨5,0,0⟩,[-20480,516096,-3457024,-16867328,377843712,-2487697408,9332195328,-23268999168,40428474368,-46731534336,29708697600,27009024,-12734869504]),(⟨5,0,1⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨5,0,2⟩,[16384,-360448,1392640,23986176,-280723456,1181679616,-1963425792,-781320192,7800045568,-11413061632,6237077504]),(⟨5,1,0⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨5,1,1⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨5,2,0⟩,[16384,-360448,1392640,23986176,-280723456,1181679616,-1963425792,-781320192,7800045568,-11413061632,6237077504]),(⟨6,0,0⟩,[-8192,253952,-2252800,-4218880,197705728,-1509900288,6432833536,-18893160448,40891670528,-63012511744,63209676800,-32678797312]),(⟨6,0,1⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨6,0,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,1,0⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨6,1,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,2,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,3,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨7,0,1⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨7,1,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856])]


theorem partial_checked16 :
    (Poly.add (Poly.add (Poly.mul chunk16 sourceRight) partial19)
      (Poly.scale (K.ofRat (-1)) partial16)).isZero := by decide +kernel

theorem partial_sound16 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 16)
      sourceRight).eval u v t=partial16.eval u v t := by
  change (Poly.mul (chunk16++(sourceLeft.drop 19))
    sourceRight).eval u v t=partial16.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound19 partial_checked16 u v t


noncomputable def chunk12 : Poly := [(⟨1,0,4⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[0,-512,7168,-29184,30720,51712,-177152,182784]),(⟨1,4,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[-64,512,4416,-54912,194112,-323840,260288,-31360])]

noncomputable def partial12 : Poly := [(⟨1,0,4⟩,[32768,-1007616,12926976,-90775552,384811008,-1013563392,1549565952,-548028416,-4087873536,12860989440,-19206881280,12796387328,-1448624128]),(⟨1,0,5⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨1,0,6⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨1,0,7⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨1,1,0⟩,[0,131072,-4292608,60162048,-478609408,2420572160,-8222048256,18924503040,-26751401984,6627524608,77570605056,-228769923072,359172472832,-338648170496,165145640960,-17383489536]),(⟨1,1,1⟩,[0,32768,-1409024,23920640,-218169344,1216708608,-4447436800,10962731008,-17095852032,7976222720,41283321856,-136480227328,220603547648,-204244877312,89011421184]),(⟨1,1,2⟩,[0,-163840,4784128,-56295424,346750976,-1219198976,2436497408,-1937899520,-4022992896,16554819584,-26687504384,21458911232,-2410741760,-8761933824]),(⟨1,1,3⟩,[0,-65536,2293760,-30998528,214892544,-863109120,2160459776,-3278503936,852885504,10570891264,-28695920640,37256101888,-22483894272]),(⟨1,1,4⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨1,1,5⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨1,2,0⟩,[0,32768,-1409024,23920640,-218169344,1216708608,-4447436800,10962731008,-17095852032,7976222720,41283321856,-136480227328,220603547648,-204244877312,89011421184]),(⟨1,2,1⟩,[0,0,0,-524288,13631488,-133693440,591396864,-894435328,-1822425088,8641314816,-9525264384,-7216824320,28325183488,-22273327104]),(⟨1,2,4⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨1,2,6⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,3,0⟩,[0,-163840,4784128,-56295424,346750976,-1219198976,2436497408,-1937899520,-4022992896,16554819584,-26687504384,21458911232,-2410741760,-8761933824]),(⟨1,3,2⟩,[0,131072,-3407872,33423360,-147849216,223608832,455606272,-2160328704,2381316096,1804206080,-7081295872,5568331776]),(⟨1,3,4⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨1,4,0⟩,[32768,-1073152,15220736,-121774080,599703552,-1876672512,3710025728,-3826532352,-3234988032,23431880704,-47902801920,50052489216,-23932518400]),(⟨1,4,1⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨1,4,2⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨1,4,3⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨1,5,0⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨1,5,1⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨1,6,0⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨1,6,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,7,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨2,0,0⟩,[16384,-438272,3612672,7634944,-371466240,3373502464,-17828249600,65140244480,-177012604928,369757876224,-593243136000,705159593984,-575099379712,274575765504,-50197676032,2982461440]),(⟨2,0,1⟩,[4096,-151552,1761280,-1982464,-136425472,1521479680,-8861966336,34471870464,-98409205760,214289911808,-354323423232,425780527104,-339613388800,146995007488,-15271567360]),(⟨2,0,2⟩,[-20480,475136,-2588672,-23748608,403124224,-2524897280,9293430784,-22968516608,39811878912,-46436483072,30625562624,-2296111104,-10606604288,1503272960]),(⟨2,0,3⟩,[-8192,237568,-1810432,-8331264,215416832,-1547026432,6452723712,-18751700992,40342773760,-62227996672,63117778944,-34670813184,3857530880]),(⟨2,0,4⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨2,0,5⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨2,1,0⟩,[4096,-118784,352256,21938176,-354594816,2738188288,-13309403136,45434601472,-115505057792,222266134528,-313040101376,289300299776,-119009841152,-57249869824,73739853824]),(⟨2,1,1⟩,[0,0,-65536,786432,9895936,-230817792,1627258880,-5197791232,5824184320,9309519872,-36735614976,40876900352,-4548526080,-18451922944]),(⟨2,1,4⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨2,2,0⟩,[-20480,475136,-2588672,-24272896,416755712,-2658590720,9884827648,-23862951936,37989453824,-37795168256,21100298240,-9512935424,17718579200,-20770054144]),(⟨2,2,2⟩,[16384,-327680,933888,24281088,-258965504,1075838976,-1911652352,-167051264,6802587648,-12023431168,8218427392,-955351040]),(⟨2,3,0⟩,[-8192,237568,-1810432,-8331264,215416832,-1547026432,6452723712,-18751700992,40342773760,-62227996672,63117778944,-34670813184,3857530880]),(⟨2,4,0⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨2,4,1⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨2,5,0⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨3,0,0⟩,[20480,-622592,6184960,-2703360,-460869632,4738662400,-26405404672,99559768064,-276730040320,588174655488,-953847390208,1133228572672,-903229517824,394028007424,-40537276416]),(⟨3,0,1⟩,[4096,-159744,1982464,-4308992,-116666368,1337937920,-7648903168,30071783424,-91405635584,217381416960,-385635139584,475939651584,-365599166464,133193396224]),(⟨3,0,2⟩,[-20480,516096,-3457024,-16867328,377843712,-2487697408,9332195328,-23268999168,40428474368,-46731534336,29708697600,27009024,-12734869504]),(⟨3,0,3⟩,[-8192,253952,-2252800,-4218880,197705728,-1509900288,6432833536,-18893160448,40891670528,-63012511744,63209676800,-32678797312]),(⟨3,0,4⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨3,0,6⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,1,0⟩,[4096,-323584,6766592,-60604416,230084608,118738944,-5212405760,28133883904,-95428628480,233936236544,-412322643968,497398562816,-368009908224,124431462400]),(⟨3,1,1⟩,[0,0,-65536,1441792,-6094848,-83361792,1015939072,-4386979840,7959609344,495452160,-28136243200,50144346112,-32372752384]),(⟨3,1,2⟩,[0,131072,-3407872,33423360,-147849216,223608832,455606272,-2160328704,2381316096,1804206080,-7081295872,5568331776]),(⟨3,2,0⟩,[-20480,516096,-3457024,-16867328,377843712,-2487697408,9332195328,-23268999168,40428474368,-46731534336,29708697600,27009024,-12734869504]),(⟨3,2,2⟩,[16384,-360448,1523712,20840448,-253984768,1096744960,-1989902336,-123863040,7034060800,-12536086528,8093188096]),(⟨3,2,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,3,0⟩,[-8192,385024,-5660672,29204480,49856512,-1286291456,6888439808,-21053489152,43272986624,-61208305664,56128380928,-27110465536]),(⟨3,4,0⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨3,4,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,6,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,0,0⟩,[-16384,315392,-540672,-29368320,290193408,-1089835008,608665600,11406622720,-59240366080,170276728832,-327799226368,425549815808,-343332061184,130875265024]),(⟨4,0,1⟩,[32768,-1007616,12861440,-89333760,378716160,-1096925184,2565505024,-4935008256,3871735808,13356441600,-47343124480,62940733440,-33821376512]),(⟨4,0,2⟩,[24576,-663552,6217728,-18685952,-56573952,497664000,-934494208,-752173056,4694925312,-4162560000,-3856900096,6462267392]),(⟨4,0,3⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨4,0,4⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨4,1,0⟩,[32768,-1073152,15155200,-120332288,593608704,-1960034304,4725964800,-8213512192,4724621312,23927332864,-76039045120,100196835328,-56305270784]),(⟨4,1,1⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨4,1,2⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨4,1,3⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨4,2,0⟩,[24576,-663552,6217728,-18685952,-56573952,497664000,-934494208,-752173056,4694925312,-4162560000,-3856900096,6462267392]),(⟨4,2,1⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨4,2,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,3,0⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨4,3,1⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨4,3,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,4,0⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨5,0,0⟩,[-28672,753664,-5267456,-25198592,593260544,-4034723840,15784919040,-42020700160,80771248128,-108959531008,92826476544,-34643804160,-8877338624]),(⟨5,0,1⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨5,0,2⟩,[16384,-360448,1392640,23986176,-280723456,1181679616,-1963425792,-781320192,7800045568,-11413061632,6237077504]),(⟨5,1,0⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨5,1,1⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨5,2,0⟩,[16384,-360448,1392640,23986176,-280723456,1181679616,-1963425792,-781320192,7800045568,-11413061632,6237077504]),(⟨6,0,0⟩,[-8192,253952,-2252800,-4218880,197705728,-1509900288,6432833536,-18893160448,40891670528,-63012511744,63209676800,-32678797312]),(⟨6,0,1⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨6,0,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,1,0⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨6,1,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,2,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,3,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨7,0,1⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨7,1,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial16)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 16))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound16 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨0,3,0⟩,[-64,640,3648,-54528,197696,-331136,265664]),(⟨0,4,1⟩,[-128,1536,-3840,-4608,15232]),(⟨1,0,0⟩,[64,-1024,3136,27008,-255680,943360,-1884224,2076032,-1072512]),(⟨1,0,1⟩,[0,-512,7168,-29184,30720,51712,-177152,182784])]

noncomputable def partial8 : Poly := [(⟨0,3,0⟩,[16384,-471040,4423680,-720896,-324444160,3217182720,-17543438336,65087897600,-178320834560,373884743680,-599523966976,707448045568,-563616129024,247032999936,-25265709056]),(⟨0,3,1⟩,[4096,-159744,2048000,-5619712,-112930816,1435062272,-8684765184,34375139328,-99052244992,216713211904,-358424788992,427845926912,-332725456896,129371992064]),(⟨0,3,2⟩,[-20480,516096,-3457024,-16867328,377843712,-2487697408,9332195328,-23268999168,40428474368,-46731534336,29708697600,27009024,-12734869504]),(⟨0,3,3⟩,[-8192,253952,-2252800,-4218880,197705728,-1509900288,6432833536,-18893160448,40891670528,-63012511744,63209676800,-32678797312]),(⟨0,4,0⟩,[4096,-159744,2048000,-5619712,-112930816,1435062272,-8684765184,34375139328,-99052244992,216713211904,-358424788992,427845926912,-332725456896,129371992064]),(⟨0,4,1⟩,[32768,-1007616,12861440,-89333760,378716160,-1096925184,2565505024,-4935008256,3871735808,13356441600,-47343124480,62940733440,-33821376512]),(⟨0,4,2⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨0,4,3⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨0,4,4⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨0,5,0⟩,[-20480,516096,-3457024,-16867328,377843712,-2487697408,9332195328,-23268999168,40428474368,-46731534336,29708697600,27009024,-12734869504]),(⟨0,5,1⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨0,5,2⟩,[16384,-360448,1392640,23986176,-280723456,1181679616,-1963425792,-781320192,7800045568,-11413061632,6237077504]),(⟨0,6,0⟩,[-8192,253952,-2252800,-4218880,197705728,-1509900288,6432833536,-18893160448,40891670528,-63012511744,63209676800,-32678797312]),(⟨0,6,1⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨0,6,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨0,7,1⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨1,0,0⟩,[-16384,569344,-8003584,54042624,-91086848,-1530974208,16035561472,-87586168832,330316529664,-935764881408,2061372121088,-3554349260800,4708986953728,-4574400278528,2978403483648,-1067597963264,102000181248]),(⟨1,0,1⟩,[-4096,315392,-7487488,86695936,-558632960,1915965440,-1068122112,-24326938624,146925080576,-509477031936,1259897143296,-2329246162944,3187276861440,-3071923294208,1868365545472,-539671093248]),(⟨1,0,2⟩,[20480,-606208,6086656,-10084352,-301232128,3163955200,-16744767488,57737035776,-139833544704,239728132096,-270060118016,136369315840,108638154752,-239788351488,140423356416]),(⟨1,0,3⟩,[8192,-466944,8937472,-79831040,336969728,-209977344,-5027348480,30299766784,-102034989056,238854266880,-402336980992,471988854784,-348522381312,123165622272]),(⟨1,0,4⟩,[32768,-1073152,15220736,-121774080,599703552,-1876672512,3710025728,-3826532352,-3234988032,23431880704,-47902801920,50052489216,-23932518400]),(⟨1,0,5⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨1,0,6⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨1,0,7⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨1,1,0⟩,[-4096,315392,-7487488,86695936,-558632960,1915965440,-1068122112,-24326938624,146925080576,-509477031936,1259897143296,-2329246162944,3187276861440,-3071923294208,1868365545472,-539671093248]),(⟨1,1,1⟩,[0,65536,-2752512,46006272,-418578432,2393440256,-9437773824,27103330304,-54954164224,57495191552,64006914048,-380419833856,714394370048,-701003792384,308714864640]),(⟨1,1,2⟩,[0,-163840,4784128,-56819712,360382464,-1352892416,3027894272,-2832334848,-5845417984,25196134400,-36212768768,14242086912,25914441728,-31035260928]),(⟨1,1,3⟩,[0,-65536,2293760,-30998528,214892544,-863109120,2160459776,-3278503936,852885504,10570891264,-28695920640,37256101888,-22483894272]),(⟨1,1,4⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨1,1,5⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨1,2,0⟩,[20480,-606208,6086656,-10084352,-301232128,3163955200,-16744767488,57737035776,-139833544704,239728132096,-270060118016,136369315840,108638154752,-239788351488,140423356416]),(⟨1,2,1⟩,[0,-163840,4784128,-56819712,360382464,-1352892416,3027894272,-2832334848,-5845417984,25196134400,-36212768768,14242086912,25914441728,-31035260928]),(⟨1,2,2⟩,[-16384,458752,-4440064,9994240,135725056,-1294467072,5190615040,-10385686528,4639932416,26864844800,-68296818688,73128509440,-32673005568]),(⟨1,2,3⟩,[0,131072,-3407872,33423360,-147849216,223608832,455606272,-2160328704,2381316096,1804206080,-7081295872,5568331776]),(⟨1,2,4⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨1,2,6⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,3,0⟩,[12288,-626688,10985472,-85450752,224038912,1225084928,-13712113664,64674906112,-201087234048,455567478784,-760761769984,899834781696,-681247838208,252537614336]),(⟨1,3,1⟩,[0,-65536,2228224,-29556736,208797696,-946470912,3176398848,-7665483776,8812494848,11066343424,-56832163840,87400448000,-54856646656]),(⟨1,3,2⟩,[0,131072,-3407872,33423360,-147849216,223608832,455606272,-2160328704,2381316096,1804206080,-7081295872,5568331776]),(⟨1,3,4⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨1,4,0⟩,[32768,-1073152,15155200,-120332288,593608704,-1960034304,4725964800,-8213512192,4724621312,23927332864,-76039045120,100196835328,-56305270784]),(⟨1,4,1⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨1,4,2⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨1,4,3⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨1,5,0⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨1,5,1⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨1,6,0⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨1,6,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,7,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨2,0,0⟩,[12288,-253952,417792,34168832,-451489792,2868895744,-10674323456,21888802816,-3336122368,-146346680320,589083402240,-1395316645888,2253005008896,-2458699358208,1653022228480,-519305142272]),(⟨2,0,1⟩,[4096,-118784,417792,20103168,-336834560,2698211328,-13852303360,50612469760,-136267517952,263808880640,-331599831040,181840920576,154177433600,-349763907584,204431876096]),(⟨2,0,2⟩,[-20480,475136,-2588672,-24272896,416755712,-2658590720,9884827648,-23862951936,37989453824,-37795168256,21100298240,-9512935424,17718579200,-20770054144]),(⟨2,0,3⟩,[-8192,237568,-1810432,-8331264,215416832,-1547026432,6452723712,-18751700992,40342773760,-62227996672,63117778944,-34670813184,3857530880]),(⟨2,0,4⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨2,0,5⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨2,1,0⟩,[4096,-118784,417792,20103168,-336834560,2698211328,-13852303360,50612469760,-136267517952,263808880640,-331599831040,181840920576,154177433600,-349763907584,204431876096]),(⟨2,1,1⟩,[0,0,-65536,262144,23527424,-364511232,2218655744,-6092226560,4001759232,17950834688,-46260879360,33660076032,23776657408,-40725250048]),(⟨2,1,4⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨2,2,0⟩,[-20480,475136,-2588672,-24272896,416755712,-2658590720,9884827648,-23862951936,37989453824,-37795168256,21100298240,-9512935424,17718579200,-20770054144]),(⟨2,2,2⟩,[16384,-327680,933888,24281088,-258965504,1075838976,-1911652352,-167051264,6802587648,-12023431168,8218427392,-955351040]),(⟨2,3,0⟩,[-28672,753664,-5267456,-25198592,593260544,-4034723840,15784919040,-42020700160,80771248128,-108959531008,92826476544,-34643804160,-8877338624]),(⟨2,3,2⟩,[16384,-360448,1523712,20840448,-253984768,1096744960,-1989902336,-123863040,7034060800,-12536086528,8093188096]),(⟨2,4,0⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨2,4,1⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨2,4,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,5,0⟩,[16384,-360448,1392640,23986176,-280723456,1181679616,-1963425792,-781320192,7800045568,-11413061632,6237077504]),(⟨2,6,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,0,0⟩,[40960,-1261568,13680640,-36708352,-543932416,6685908992,-38702735360,146334072832,-399467732992,819926564864,-1265190830080,1406078115840,-1015194910720,358484533248,10874658816]),(⟨3,0,1⟩,[4096,-323584,6766592,-60604416,230084608,118738944,-5212405760,28133883904,-95428628480,233936236544,-412322643968,497398562816,-368009908224,124431462400]),(⟨3,0,2⟩,[-36864,974848,-7897088,-6873088,513568768,-3782164480,14522810368,-33654685696,45068406784,-19866689536,-38588121088,73155518464,-45407875072]),(⟨3,0,3⟩,[-8192,385024,-5660672,29204480,49856512,-1286291456,6888439808,-21053489152,43272986624,-61208305664,56128380928,-27110465536]),(⟨3,0,4⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨3,0,6⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,1,0⟩,[4096,-323584,6766592,-60604416,230084608,118738944,-5212405760,28133883904,-95428628480,233936236544,-412322643968,497398562816,-368009908224,124431462400]),(⟨3,1,1⟩,[0,0,-65536,1441792,-6094848,-83361792,1015939072,-4386979840,7959609344,495452160,-28136243200,50144346112,-32372752384]),(⟨3,1,2⟩,[0,131072,-3407872,33423360,-147849216,223608832,455606272,-2160328704,2381316096,1804206080,-7081295872,5568331776]),(⟨3,2,0⟩,[-36864,974848,-7897088,-6873088,513568768,-3782164480,14522810368,-33654685696,45068406784,-19866689536,-38588121088,73155518464,-45407875072]),(⟨3,2,1⟩,[0,131072,-3407872,33423360,-147849216,223608832,455606272,-2160328704,2381316096,1804206080,-7081295872,5568331776]),(⟨3,2,2⟩,[16384,-360448,1523712,20840448,-253984768,1096744960,-1989902336,-123863040,7034060800,-12536086528,8093188096]),(⟨3,2,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,3,0⟩,[-16384,638976,-7913472,24985600,247562240,-2796191744,13321273344,-39946649600,84164657152,-124220817408,119338057728,-59789262848]),(⟨3,4,0⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨3,4,1⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨3,4,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,6,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,0,0⟩,[-8192,12288,3612672,-52903936,280412160,-80613376,-6855180288,43644289024,-157252362240,392576176128,-703448702976,876079759360,-689443700736,262802821120]),(⟨4,0,1⟩,[32768,-1073152,15155200,-120332288,593608704,-1960034304,4725964800,-8213512192,4724621312,23927332864,-76039045120,100196835328,-56305270784]),(⟨4,0,2⟩,[24576,-663552,6217728,-18685952,-56573952,497664000,-934494208,-752173056,4694925312,-4162560000,-3856900096,6462267392]),(⟨4,0,3⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨4,0,4⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨4,1,0⟩,[32768,-1073152,15155200,-120332288,593608704,-1960034304,4725964800,-8213512192,4724621312,23927332864,-76039045120,100196835328,-56305270784]),(⟨4,1,1⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨4,1,2⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨4,1,3⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨4,2,0⟩,[24576,-663552,6217728,-18685952,-56573952,497664000,-934494208,-752173056,4694925312,-4162560000,-3856900096,6462267392]),(⟨4,2,1⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨4,2,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,3,0⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨4,3,1⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨4,3,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,4,0⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨5,0,0⟩,[-28672,753664,-5267456,-25198592,593260544,-4034723840,15784919040,-42020700160,80771248128,-108959531008,92826476544,-34643804160,-8877338624]),(⟨5,0,1⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨5,0,2⟩,[16384,-360448,1392640,23986176,-280723456,1181679616,-1963425792,-781320192,7800045568,-11413061632,6237077504]),(⟨5,1,0⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨5,1,1⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨5,2,0⟩,[16384,-360448,1392640,23986176,-280723456,1181679616,-1963425792,-781320192,7800045568,-11413061632,6237077504]),(⟨6,0,0⟩,[-8192,253952,-2252800,-4218880,197705728,-1509900288,6432833536,-18893160448,40891670528,-63012511744,63209676800,-32678797312]),(⟨6,0,1⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨6,0,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,1,0⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨6,1,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,2,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,3,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨7,0,1⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨7,1,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,1,0⟩,[64,-1024,3136,27008,-255680,943360,-1884224,2076032,-1072512]),(⟨0,1,1⟩,[0,-512,7168,-29184,30720,51712,-177152,182784]),(⟨0,1,4⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[-64,512,4416,-54912,194112,-323840,260288,-31360])]

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[-16384,569344,-8003584,54042624,-91086848,-1530974208,16035561472,-87586168832,330316529664,-935764881408,2061372121088,-3554349260800,4708986953728,-4574400278528,2978403483648,-1067597963264,102000181248]),(⟨0,1,1⟩,[-4096,315392,-7487488,86695936,-558632960,1915965440,-1068122112,-24326938624,146925080576,-509477031936,1259897143296,-2329246162944,3187276861440,-3071923294208,1868365545472,-539671093248]),(⟨0,1,2⟩,[20480,-606208,6086656,-10084352,-301232128,3163955200,-16744767488,57737035776,-139833544704,239728132096,-270060118016,136369315840,108638154752,-239788351488,140423356416]),(⟨0,1,3⟩,[8192,-466944,8937472,-79831040,336969728,-209977344,-5027348480,30299766784,-102034989056,238854266880,-402336980992,471988854784,-348522381312,123165622272]),(⟨0,1,4⟩,[32768,-1073152,15220736,-121774080,599703552,-1876672512,3710025728,-3826532352,-3234988032,23431880704,-47902801920,50052489216,-23932518400]),(⟨0,1,5⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨0,1,6⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨0,1,7⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨0,2,0⟩,[12288,-253952,417792,34168832,-451489792,2868895744,-10674323456,21888802816,-3336122368,-146346680320,589083402240,-1395316645888,2253005008896,-2458699358208,1653022228480,-519305142272]),(⟨0,2,1⟩,[4096,-118784,417792,20103168,-336834560,2698211328,-13852303360,50612469760,-136267517952,263808880640,-331599831040,181840920576,154177433600,-349763907584,204431876096]),(⟨0,2,2⟩,[-20480,475136,-2588672,-24272896,416755712,-2658590720,9884827648,-23862951936,37989453824,-37795168256,21100298240,-9512935424,17718579200,-20770054144]),(⟨0,2,3⟩,[-8192,237568,-1810432,-8331264,215416832,-1547026432,6452723712,-18751700992,40342773760,-62227996672,63117778944,-34670813184,3857530880]),(⟨0,2,4⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨0,2,5⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨0,3,0⟩,[40960,-1261568,13680640,-36708352,-543932416,6685908992,-38702735360,146334072832,-399467732992,819926564864,-1265190830080,1406078115840,-1015194910720,358484533248,10874658816]),(⟨0,3,1⟩,[4096,-323584,6766592,-60604416,230084608,118738944,-5212405760,28133883904,-95428628480,233936236544,-412322643968,497398562816,-368009908224,124431462400]),(⟨0,3,2⟩,[-36864,974848,-7897088,-6873088,513568768,-3782164480,14522810368,-33654685696,45068406784,-19866689536,-38588121088,73155518464,-45407875072]),(⟨0,3,3⟩,[-8192,385024,-5660672,29204480,49856512,-1286291456,6888439808,-21053489152,43272986624,-61208305664,56128380928,-27110465536]),(⟨0,3,4⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨0,3,6⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨0,4,0⟩,[-8192,12288,3612672,-52903936,280412160,-80613376,-6855180288,43644289024,-157252362240,392576176128,-703448702976,876079759360,-689443700736,262802821120]),(⟨0,4,1⟩,[32768,-1073152,15155200,-120332288,593608704,-1960034304,4725964800,-8213512192,4724621312,23927332864,-76039045120,100196835328,-56305270784]),(⟨0,4,2⟩,[24576,-663552,6217728,-18685952,-56573952,497664000,-934494208,-752173056,4694925312,-4162560000,-3856900096,6462267392]),(⟨0,4,3⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨0,4,4⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨0,5,0⟩,[-28672,753664,-5267456,-25198592,593260544,-4034723840,15784919040,-42020700160,80771248128,-108959531008,92826476544,-34643804160,-8877338624]),(⟨0,5,1⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨0,5,2⟩,[16384,-360448,1392640,23986176,-280723456,1181679616,-1963425792,-781320192,7800045568,-11413061632,6237077504]),(⟨0,6,0⟩,[-8192,253952,-2252800,-4218880,197705728,-1509900288,6432833536,-18893160448,40891670528,-63012511744,63209676800,-32678797312]),(⟨0,6,1⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨0,6,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨0,7,1⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨1,0,0⟩,[-16384,569344,-8003584,54042624,-91086848,-1530974208,16035561472,-87586168832,330316529664,-935764881408,2061372121088,-3554349260800,4708986953728,-4574400278528,2978403483648,-1067597963264,102000181248]),(⟨1,0,1⟩,[-4096,315392,-7487488,86695936,-558632960,1915965440,-1068122112,-24326938624,146925080576,-509477031936,1259897143296,-2329246162944,3187276861440,-3071923294208,1868365545472,-539671093248]),(⟨1,0,2⟩,[20480,-606208,6086656,-10084352,-301232128,3163955200,-16744767488,57737035776,-139833544704,239728132096,-270060118016,136369315840,108638154752,-239788351488,140423356416]),(⟨1,0,3⟩,[8192,-466944,8937472,-79831040,336969728,-209977344,-5027348480,30299766784,-102034989056,238854266880,-402336980992,471988854784,-348522381312,123165622272]),(⟨1,0,4⟩,[32768,-1073152,15220736,-121774080,599703552,-1876672512,3710025728,-3826532352,-3234988032,23431880704,-47902801920,50052489216,-23932518400]),(⟨1,0,5⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨1,0,6⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨1,0,7⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨1,1,0⟩,[-8192,499712,-10682368,113229824,-638656512,1411358720,6085804032,-67578380288,320601563136,-1025581588480,2442223681536,-4429722402816,6015381250048,-5805198417920,3571585449984,-1061958696960]),(⟨1,1,1⟩,[0,98304,-4096000,68091904,-618987520,3570171904,-14428110848,43243929600,-92812476416,107014160384,86730506240,-624359440384,1208185192448,-1197762707456,528418308096]),(⟨1,1,2⟩,[0,-163840,4784128,-57344000,374013952,-1486585856,3619291136,-3726770176,-7667843072,33837449216,-45738033152,7025262592,54239625216,-53308588032]),(⟨1,1,3⟩,[0,-65536,2293760,-30998528,214892544,-863109120,2160459776,-3278503936,852885504,10570891264,-28695920640,37256101888,-22483894272]),(⟨1,1,4⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨1,1,5⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨1,2,0⟩,[24576,-757760,7913472,-13901824,-419897344,4645457920,-26149634048,97386774528,-259005210624,495560790016,-642943270912,454690463744,42212040704,-385307381760,255843811328]),(⟨1,2,1⟩,[0,-163840,4718592,-56033280,370278400,-1583710208,4655153152,-8030126080,-21233664,34505654272,-72948383744,55118987264,21365915648,-49487183872]),(⟨1,2,2⟩,[-16384,458752,-4440064,9994240,135725056,-1294467072,5190615040,-10385686528,4639932416,26864844800,-68296818688,73128509440,-32673005568]),(⟨1,2,3⟩,[0,131072,-3407872,33423360,-147849216,223608832,455606272,-2160328704,2381316096,1804206080,-7081295872,5568331776]),(⟨1,2,4⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨1,2,6⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,3,0⟩,[12288,-626688,10919936,-84140032,220303360,1127960576,-12676251648,60371550208,-193440624640,456235683840,-787972120576,947928506368,-714121547776,256359018496]),(⟨1,3,1⟩,[0,-65536,2228224,-29556736,208797696,-946470912,3176398848,-7665483776,8812494848,11066343424,-56832163840,87400448000,-54856646656]),(⟨1,3,2⟩,[0,131072,-3407872,33423360,-147849216,223608832,455606272,-2160328704,2381316096,1804206080,-7081295872,5568331776]),(⟨1,3,4⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨1,4,0⟩,[32768,-1073152,15155200,-120332288,593608704,-1960034304,4725964800,-8213512192,4724621312,23927332864,-76039045120,100196835328,-56305270784]),(⟨1,4,1⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨1,4,2⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨1,4,3⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨1,5,0⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨1,5,1⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨1,6,0⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨1,6,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,7,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨2,0,0⟩,[12288,-253952,417792,34168832,-451489792,2868895744,-10674323456,21888802816,-3336122368,-146346680320,589083402240,-1395316645888,2253005008896,-2458699358208,1653022228480,-519305142272]),(⟨2,0,1⟩,[4096,-118784,417792,20103168,-336834560,2698211328,-13852303360,50612469760,-136267517952,263808880640,-331599831040,181840920576,154177433600,-349763907584,204431876096]),(⟨2,0,2⟩,[-20480,475136,-2588672,-24272896,416755712,-2658590720,9884827648,-23862951936,37989453824,-37795168256,21100298240,-9512935424,17718579200,-20770054144]),(⟨2,0,3⟩,[-8192,237568,-1810432,-8331264,215416832,-1547026432,6452723712,-18751700992,40342773760,-62227996672,63117778944,-34670813184,3857530880]),(⟨2,0,4⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨2,0,5⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨2,1,0⟩,[24576,-757760,7913472,-13901824,-419897344,4645457920,-26149634048,97386774528,-259005210624,495560790016,-642943270912,454690463744,42212040704,-385307381760,255843811328]),(⟨2,1,1⟩,[0,-163840,4718592,-56033280,370278400,-1583710208,4655153152,-8030126080,-21233664,34505654272,-72948383744,55118987264,21365915648,-49487183872]),(⟨2,1,2⟩,[-16384,458752,-4440064,9994240,135725056,-1294467072,5190615040,-10385686528,4639932416,26864844800,-68296818688,73128509440,-32673005568]),(⟨2,1,3⟩,[0,131072,-3407872,33423360,-147849216,223608832,455606272,-2160328704,2381316096,1804206080,-7081295872,5568331776]),(⟨2,1,4⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨2,1,6⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,2,0⟩,[-40960,950272,-5177344,-48021504,819879936,-5183488000,19178258432,-46831468544,77801332736,-84231651328,51725860864,-11809046528,7111974912,-19266781184]),(⟨2,2,2⟩,[32768,-655360,1867776,48562176,-517931008,2151677952,-3823304704,-334102528,13605175296,-24046862336,16436854784,-1910702080]),(⟨2,3,0⟩,[-45056,1212416,-9707520,-15204352,728985600,-5329190912,20975534080,-52406386688,85411180544,-82094686208,24529657856,38484705280,-41550344192]),(⟨2,3,1⟩,[0,131072,-3407872,33423360,-147849216,223608832,455606272,-2160328704,2381316096,1804206080,-7081295872,5568331776]),(⟨2,3,2⟩,[16384,-360448,1523712,20840448,-253984768,1096744960,-1989902336,-123863040,7034060800,-12536086528,8093188096]),(⟨2,3,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,4,0⟩,[24576,-663552,6217728,-18685952,-56573952,497664000,-934494208,-752173056,4694925312,-4162560000,-3856900096,6462267392]),(⟨2,4,1⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨2,4,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,5,0⟩,[16384,-360448,1392640,23986176,-280723456,1181679616,-1963425792,-781320192,7800045568,-11413061632,6237077504]),(⟨2,6,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,0,0⟩,[40960,-1261568,13680640,-36708352,-543932416,6685908992,-38702735360,146334072832,-399467732992,819926564864,-1265190830080,1406078115840,-1015194910720,358484533248,10874658816]),(⟨3,0,1⟩,[4096,-323584,6766592,-60604416,230084608,118738944,-5212405760,28133883904,-95428628480,233936236544,-412322643968,497398562816,-368009908224,124431462400]),(⟨3,0,2⟩,[-36864,974848,-7897088,-6873088,513568768,-3782164480,14522810368,-33654685696,45068406784,-19866689536,-38588121088,73155518464,-45407875072]),(⟨3,0,3⟩,[-8192,385024,-5660672,29204480,49856512,-1286291456,6888439808,-21053489152,43272986624,-61208305664,56128380928,-27110465536]),(⟨3,0,4⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨3,0,6⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,1,0⟩,[12288,-626688,10919936,-84140032,220303360,1127960576,-12676251648,60371550208,-193440624640,456235683840,-787972120576,947928506368,-714121547776,256359018496]),(⟨3,1,1⟩,[0,-65536,2228224,-29556736,208797696,-946470912,3176398848,-7665483776,8812494848,11066343424,-56832163840,87400448000,-54856646656]),(⟨3,1,2⟩,[0,131072,-3407872,33423360,-147849216,223608832,455606272,-2160328704,2381316096,1804206080,-7081295872,5568331776]),(⟨3,1,4⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨3,2,0⟩,[-45056,1212416,-9707520,-15204352,728985600,-5329190912,20975534080,-52406386688,85411180544,-82094686208,24529657856,38484705280,-41550344192]),(⟨3,2,1⟩,[0,131072,-3407872,33423360,-147849216,223608832,455606272,-2160328704,2381316096,1804206080,-7081295872,5568331776]),(⟨3,2,2⟩,[16384,-360448,1523712,20840448,-253984768,1096744960,-1989902336,-123863040,7034060800,-12536086528,8093188096]),(⟨3,2,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,3,0⟩,[-16384,638976,-7913472,24985600,247562240,-2796191744,13321273344,-39946649600,84164657152,-124220817408,119338057728,-59789262848]),(⟨3,4,0⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨3,4,1⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨3,4,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,6,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,0,0⟩,[-8192,12288,3612672,-52903936,280412160,-80613376,-6855180288,43644289024,-157252362240,392576176128,-703448702976,876079759360,-689443700736,262802821120]),(⟨4,0,1⟩,[32768,-1073152,15155200,-120332288,593608704,-1960034304,4725964800,-8213512192,4724621312,23927332864,-76039045120,100196835328,-56305270784]),(⟨4,0,2⟩,[24576,-663552,6217728,-18685952,-56573952,497664000,-934494208,-752173056,4694925312,-4162560000,-3856900096,6462267392]),(⟨4,0,3⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨4,0,4⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨4,1,0⟩,[32768,-1073152,15155200,-120332288,593608704,-1960034304,4725964800,-8213512192,4724621312,23927332864,-76039045120,100196835328,-56305270784]),(⟨4,1,1⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨4,1,2⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨4,1,3⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨4,2,0⟩,[24576,-663552,6217728,-18685952,-56573952,497664000,-934494208,-752173056,4694925312,-4162560000,-3856900096,6462267392]),(⟨4,2,1⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨4,2,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,3,0⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨4,3,1⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨4,3,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,4,0⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨5,0,0⟩,[-28672,753664,-5267456,-25198592,593260544,-4034723840,15784919040,-42020700160,80771248128,-108959531008,92826476544,-34643804160,-8877338624]),(⟨5,0,1⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨5,0,2⟩,[16384,-360448,1392640,23986176,-280723456,1181679616,-1963425792,-781320192,7800045568,-11413061632,6237077504]),(⟨5,1,0⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨5,1,1⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨5,2,0⟩,[16384,-360448,1392640,23986176,-280723456,1181679616,-1963425792,-781320192,7800045568,-11413061632,6237077504]),(⟨6,0,0⟩,[-8192,253952,-2252800,-4218880,197705728,-1509900288,6432833536,-18893160448,40891670528,-63012511744,63209676800,-32678797312]),(⟨6,0,1⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨6,0,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,1,0⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨6,1,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,2,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,3,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨7,0,1⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨7,1,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,0⟩,[64,-768,-1856,71168,-470336,1581440,-3104960,3581696,-2132736,328832]),(⟨0,0,1⟩,[64,-1024,3136,27008,-255680,943360,-1884224,2076032,-1072512]),(⟨0,0,2⟩,[-64,512,4416,-54912,194112,-323840,260288,-31360]),(⟨0,0,3⟩,[-64,640,3648,-54528,197696,-331136,265664])]

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[-16384,503808,-5496832,9633792,391446528,-5129146368,35644850176,-169039953920,596009377792,-1629997051904,3528196726784,-6054742294528,8095543312384,-8107004145664,5662828855296,-2412798967808,469622333440,-31273238528]),(⟨0,0,1⟩,[-20480,737280,-10403840,64110592,29667328,-3670343680,32723034112,-172603080704,646306787328,-1837863321600,4085509095424,-7125441822720,9558031290368,-9415286423552,6245021212672,-2318430535680,262133473280]),(⟨0,0,2⟩,[32768,-811008,5070848,44621824,-948772864,7376502784,-34131443712,104437940224,-212679114752,244840570880,58484350976,-909133815808,2015689990144,-2479123382272,1735642890240,-535068033024]),(⟨0,0,3⟩,[49152,-1531904,16506880,-37175296,-788135936,9265700864,-53618794496,204987858944,-569965035520,1198085332992,-1900569288704,2181907136512,-1649435115520,648649940992,-29574307840]),(⟨0,0,4⟩,[-8192,12288,3612672,-52903936,280412160,-80613376,-6855180288,43644289024,-157252362240,392576176128,-703448702976,876079759360,-689443700736,262802821120]),(⟨0,0,5⟩,[-28672,753664,-5267456,-25198592,593260544,-4034723840,15784919040,-42020700160,80771248128,-108959531008,92826476544,-34643804160,-8877338624]),(⟨0,0,6⟩,[-8192,253952,-2252800,-4218880,197705728,-1509900288,6432833536,-18893160448,40891670528,-63012511744,63209676800,-32678797312]),(⟨0,1,0⟩,[-20480,737280,-10403840,64110592,29667328,-3670343680,32723034112,-172603080704,646306787328,-1837863321600,4085509095424,-7125441822720,9558031290368,-9415286423552,6245021212672,-2318430535680,262133473280]),(⟨0,1,1⟩,[-8192,499712,-10616832,111656960,-629153792,1485807616,4636540928,-57968050176,286390329344,-961189060608,2416254976000,-4600318115840,6456216559616,-6310169026560,3843594190848,-1102028849152]),(⟨0,1,2⟩,[24576,-757760,7913472,-13901824,-419897344,4645457920,-26149634048,97386774528,-259005210624,495560790016,-642943270912,454690463744,42212040704,-385307381760,255843811328]),(⟨0,1,3⟩,[12288,-626688,10919936,-84140032,220303360,1127960576,-12676251648,60371550208,-193440624640,456235683840,-787972120576,947928506368,-714121547776,256359018496]),(⟨0,1,4⟩,[32768,-1073152,15155200,-120332288,593608704,-1960034304,4725964800,-8213512192,4724621312,23927332864,-76039045120,100196835328,-56305270784]),(⟨0,1,5⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨0,1,6⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨0,1,7⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨0,2,0⟩,[32768,-811008,5070848,44621824,-948772864,7376502784,-34131443712,104437940224,-212679114752,244840570880,58484350976,-909133815808,2015689990144,-2479123382272,1735642890240,-535068033024]),(⟨0,2,1⟩,[24576,-757760,7913472,-13901824,-419897344,4645457920,-26149634048,97386774528,-259005210624,495560790016,-642943270912,454690463744,42212040704,-385307381760,255843811328]),(⟨0,2,2⟩,[-57344,1343488,-7553024,-66633728,1182195712,-7586070528,27731066880,-62929600512,84293509120,-41582723072,-58482966528,114433605632,-60890210304,-9249243136]),(⟨0,2,3⟩,[-45056,1212416,-9707520,-15204352,728985600,-5329190912,20975534080,-52406386688,85411180544,-82094686208,24529657856,38484705280,-41550344192]),(⟨0,2,4⟩,[24576,-663552,6217728,-18685952,-56573952,497664000,-934494208,-752173056,4694925312,-4162560000,-3856900096,6462267392]),(⟨0,2,5⟩,[16384,-360448,1392640,23986176,-280723456,1181679616,-1963425792,-781320192,7800045568,-11413061632,6237077504]),(⟨0,3,0⟩,[49152,-1531904,16506880,-37175296,-788135936,9265700864,-53618794496,204987858944,-569965035520,1198085332992,-1900569288704,2181907136512,-1649435115520,648649940992,-29574307840]),(⟨0,3,1⟩,[12288,-626688,10919936,-84140032,220303360,1127960576,-12676251648,60371550208,-193440624640,456235683840,-787972120576,947928506368,-714121547776,256359018496]),(⟨0,3,2⟩,[-45056,1212416,-9707520,-15204352,728985600,-5329190912,20975534080,-52406386688,85411180544,-82094686208,24529657856,38484705280,-41550344192]),(⟨0,3,3⟩,[-16384,638976,-7913472,24985600,247562240,-2796191744,13321273344,-39946649600,84164657152,-124220817408,119338057728,-59789262848]),(⟨0,3,4⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨0,3,6⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨0,4,0⟩,[-8192,12288,3612672,-52903936,280412160,-80613376,-6855180288,43644289024,-157252362240,392576176128,-703448702976,876079759360,-689443700736,262802821120]),(⟨0,4,1⟩,[32768,-1073152,15155200,-120332288,593608704,-1960034304,4725964800,-8213512192,4724621312,23927332864,-76039045120,100196835328,-56305270784]),(⟨0,4,2⟩,[24576,-663552,6217728,-18685952,-56573952,497664000,-934494208,-752173056,4694925312,-4162560000,-3856900096,6462267392]),(⟨0,4,3⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨0,4,4⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨0,5,0⟩,[-28672,753664,-5267456,-25198592,593260544,-4034723840,15784919040,-42020700160,80771248128,-108959531008,92826476544,-34643804160,-8877338624]),(⟨0,5,1⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨0,5,2⟩,[16384,-360448,1392640,23986176,-280723456,1181679616,-1963425792,-781320192,7800045568,-11413061632,6237077504]),(⟨0,6,0⟩,[-8192,253952,-2252800,-4218880,197705728,-1509900288,6432833536,-18893160448,40891670528,-63012511744,63209676800,-32678797312]),(⟨0,6,1⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨0,6,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨0,7,1⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨1,0,0⟩,[-20480,737280,-10403840,64110592,29667328,-3670343680,32723034112,-172603080704,646306787328,-1837863321600,4085509095424,-7125441822720,9558031290368,-9415286423552,6245021212672,-2318430535680,262133473280]),(⟨1,0,1⟩,[-8192,499712,-10616832,111656960,-629153792,1485807616,4636540928,-57968050176,286390329344,-961189060608,2416254976000,-4600318115840,6456216559616,-6310169026560,3843594190848,-1102028849152]),(⟨1,0,2⟩,[24576,-757760,7913472,-13901824,-419897344,4645457920,-26149634048,97386774528,-259005210624,495560790016,-642943270912,454690463744,42212040704,-385307381760,255843811328]),(⟨1,0,3⟩,[12288,-626688,10919936,-84140032,220303360,1127960576,-12676251648,60371550208,-193440624640,456235683840,-787972120576,947928506368,-714121547776,256359018496]),(⟨1,0,4⟩,[32768,-1073152,15155200,-120332288,593608704,-1960034304,4725964800,-8213512192,4724621312,23927332864,-76039045120,100196835328,-56305270784]),(⟨1,0,5⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨1,0,6⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨1,0,7⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨1,1,0⟩,[-8192,499712,-10616832,111656960,-629153792,1485807616,4636540928,-57968050176,286390329344,-961189060608,2416254976000,-4600318115840,6456216559616,-6310169026560,3843594190848,-1102028849152]),(⟨1,1,1⟩,[0,98304,-4030464,66256896,-601227264,3530194944,-14971011072,48421797888,-113574936576,148556906496,68170776576,-731818819584,1481372467200,-1490276745216,659110330368]),(⟨1,1,2⟩,[0,-163840,4718592,-56033280,370278400,-1583710208,4655153152,-8030126080,-21233664,34505654272,-72948383744,55118987264,21365915648,-49487183872]),(⟨1,1,3⟩,[0,-65536,2228224,-29556736,208797696,-946470912,3176398848,-7665483776,8812494848,11066343424,-56832163840,87400448000,-54856646656]),(⟨1,1,4⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨1,1,5⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨1,2,0⟩,[24576,-757760,7913472,-13901824,-419897344,4645457920,-26149634048,97386774528,-259005210624,495560790016,-642943270912,454690463744,42212040704,-385307381760,255843811328]),(⟨1,2,1⟩,[0,-163840,4718592,-56033280,370278400,-1583710208,4655153152,-8030126080,-21233664,34505654272,-72948383744,55118987264,21365915648,-49487183872]),(⟨1,2,2⟩,[-16384,458752,-4440064,9994240,135725056,-1294467072,5190615040,-10385686528,4639932416,26864844800,-68296818688,73128509440,-32673005568]),(⟨1,2,3⟩,[0,131072,-3407872,33423360,-147849216,223608832,455606272,-2160328704,2381316096,1804206080,-7081295872,5568331776]),(⟨1,2,4⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨1,2,6⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,3,0⟩,[12288,-626688,10919936,-84140032,220303360,1127960576,-12676251648,60371550208,-193440624640,456235683840,-787972120576,947928506368,-714121547776,256359018496]),(⟨1,3,1⟩,[0,-65536,2228224,-29556736,208797696,-946470912,3176398848,-7665483776,8812494848,11066343424,-56832163840,87400448000,-54856646656]),(⟨1,3,2⟩,[0,131072,-3407872,33423360,-147849216,223608832,455606272,-2160328704,2381316096,1804206080,-7081295872,5568331776]),(⟨1,3,4⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨1,4,0⟩,[32768,-1073152,15155200,-120332288,593608704,-1960034304,4725964800,-8213512192,4724621312,23927332864,-76039045120,100196835328,-56305270784]),(⟨1,4,1⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨1,4,2⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨1,4,3⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨1,5,0⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨1,5,1⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨1,6,0⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨1,6,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,7,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨2,0,0⟩,[32768,-811008,5070848,44621824,-948772864,7376502784,-34131443712,104437940224,-212679114752,244840570880,58484350976,-909133815808,2015689990144,-2479123382272,1735642890240,-535068033024]),(⟨2,0,1⟩,[24576,-757760,7913472,-13901824,-419897344,4645457920,-26149634048,97386774528,-259005210624,495560790016,-642943270912,454690463744,42212040704,-385307381760,255843811328]),(⟨2,0,2⟩,[-57344,1343488,-7553024,-66633728,1182195712,-7586070528,27731066880,-62929600512,84293509120,-41582723072,-58482966528,114433605632,-60890210304,-9249243136]),(⟨2,0,3⟩,[-45056,1212416,-9707520,-15204352,728985600,-5329190912,20975534080,-52406386688,85411180544,-82094686208,24529657856,38484705280,-41550344192]),(⟨2,0,4⟩,[24576,-663552,6217728,-18685952,-56573952,497664000,-934494208,-752173056,4694925312,-4162560000,-3856900096,6462267392]),(⟨2,0,5⟩,[16384,-360448,1392640,23986176,-280723456,1181679616,-1963425792,-781320192,7800045568,-11413061632,6237077504]),(⟨2,1,0⟩,[24576,-757760,7913472,-13901824,-419897344,4645457920,-26149634048,97386774528,-259005210624,495560790016,-642943270912,454690463744,42212040704,-385307381760,255843811328]),(⟨2,1,1⟩,[0,-163840,4718592,-56033280,370278400,-1583710208,4655153152,-8030126080,-21233664,34505654272,-72948383744,55118987264,21365915648,-49487183872]),(⟨2,1,2⟩,[-16384,458752,-4440064,9994240,135725056,-1294467072,5190615040,-10385686528,4639932416,26864844800,-68296818688,73128509440,-32673005568]),(⟨2,1,3⟩,[0,131072,-3407872,33423360,-147849216,223608832,455606272,-2160328704,2381316096,1804206080,-7081295872,5568331776]),(⟨2,1,4⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨2,1,6⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,2,0⟩,[-57344,1343488,-7553024,-66633728,1182195712,-7586070528,27731066880,-62929600512,84293509120,-41582723072,-58482966528,114433605632,-60890210304,-9249243136]),(⟨2,2,1⟩,[-16384,458752,-4440064,9994240,135725056,-1294467072,5190615040,-10385686528,4639932416,26864844800,-68296818688,73128509440,-32673005568]),(⟨2,2,2⟩,[49152,-983040,2801664,72843264,-776896512,3227516928,-5734957056,-501153792,20407762944,-36070293504,24655282176,-2866053120]),(⟨2,2,3⟩,[16384,-360448,1523712,20840448,-253984768,1096744960,-1989902336,-123863040,7034060800,-12536086528,8093188096]),(⟨2,3,0⟩,[-45056,1212416,-9707520,-15204352,728985600,-5329190912,20975534080,-52406386688,85411180544,-82094686208,24529657856,38484705280,-41550344192]),(⟨2,3,1⟩,[0,131072,-3407872,33423360,-147849216,223608832,455606272,-2160328704,2381316096,1804206080,-7081295872,5568331776]),(⟨2,3,2⟩,[16384,-360448,1523712,20840448,-253984768,1096744960,-1989902336,-123863040,7034060800,-12536086528,8093188096]),(⟨2,3,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,4,0⟩,[24576,-663552,6217728,-18685952,-56573952,497664000,-934494208,-752173056,4694925312,-4162560000,-3856900096,6462267392]),(⟨2,4,1⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨2,4,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,5,0⟩,[16384,-360448,1392640,23986176,-280723456,1181679616,-1963425792,-781320192,7800045568,-11413061632,6237077504]),(⟨2,6,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,0,0⟩,[49152,-1531904,16506880,-37175296,-788135936,9265700864,-53618794496,204987858944,-569965035520,1198085332992,-1900569288704,2181907136512,-1649435115520,648649940992,-29574307840]),(⟨3,0,1⟩,[12288,-626688,10919936,-84140032,220303360,1127960576,-12676251648,60371550208,-193440624640,456235683840,-787972120576,947928506368,-714121547776,256359018496]),(⟨3,0,2⟩,[-45056,1212416,-9707520,-15204352,728985600,-5329190912,20975534080,-52406386688,85411180544,-82094686208,24529657856,38484705280,-41550344192]),(⟨3,0,3⟩,[-16384,638976,-7913472,24985600,247562240,-2796191744,13321273344,-39946649600,84164657152,-124220817408,119338057728,-59789262848]),(⟨3,0,4⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨3,0,6⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,1,0⟩,[12288,-626688,10919936,-84140032,220303360,1127960576,-12676251648,60371550208,-193440624640,456235683840,-787972120576,947928506368,-714121547776,256359018496]),(⟨3,1,1⟩,[0,-65536,2228224,-29556736,208797696,-946470912,3176398848,-7665483776,8812494848,11066343424,-56832163840,87400448000,-54856646656]),(⟨3,1,2⟩,[0,131072,-3407872,33423360,-147849216,223608832,455606272,-2160328704,2381316096,1804206080,-7081295872,5568331776]),(⟨3,1,4⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨3,2,0⟩,[-45056,1212416,-9707520,-15204352,728985600,-5329190912,20975534080,-52406386688,85411180544,-82094686208,24529657856,38484705280,-41550344192]),(⟨3,2,1⟩,[0,131072,-3407872,33423360,-147849216,223608832,455606272,-2160328704,2381316096,1804206080,-7081295872,5568331776]),(⟨3,2,2⟩,[16384,-360448,1523712,20840448,-253984768,1096744960,-1989902336,-123863040,7034060800,-12536086528,8093188096]),(⟨3,2,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,3,0⟩,[-16384,638976,-7913472,24985600,247562240,-2796191744,13321273344,-39946649600,84164657152,-124220817408,119338057728,-59789262848]),(⟨3,4,0⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨3,4,1⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨3,4,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,6,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,0,0⟩,[-8192,12288,3612672,-52903936,280412160,-80613376,-6855180288,43644289024,-157252362240,392576176128,-703448702976,876079759360,-689443700736,262802821120]),(⟨4,0,1⟩,[32768,-1073152,15155200,-120332288,593608704,-1960034304,4725964800,-8213512192,4724621312,23927332864,-76039045120,100196835328,-56305270784]),(⟨4,0,2⟩,[24576,-663552,6217728,-18685952,-56573952,497664000,-934494208,-752173056,4694925312,-4162560000,-3856900096,6462267392]),(⟨4,0,3⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨4,0,4⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨4,1,0⟩,[32768,-1073152,15155200,-120332288,593608704,-1960034304,4725964800,-8213512192,4724621312,23927332864,-76039045120,100196835328,-56305270784]),(⟨4,1,1⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨4,1,2⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨4,1,3⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨4,2,0⟩,[24576,-663552,6217728,-18685952,-56573952,497664000,-934494208,-752173056,4694925312,-4162560000,-3856900096,6462267392]),(⟨4,2,1⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨4,2,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,3,0⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨4,3,1⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨4,3,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,4,0⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨5,0,0⟩,[-28672,753664,-5267456,-25198592,593260544,-4034723840,15784919040,-42020700160,80771248128,-108959531008,92826476544,-34643804160,-8877338624]),(⟨5,0,1⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨5,0,2⟩,[16384,-360448,1392640,23986176,-280723456,1181679616,-1963425792,-781320192,7800045568,-11413061632,6237077504]),(⟨5,1,0⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨5,1,1⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨5,2,0⟩,[16384,-360448,1392640,23986176,-280723456,1181679616,-1963425792,-781320192,7800045568,-11413061632,6237077504]),(⟨6,0,0⟩,[-8192,253952,-2252800,-4218880,197705728,-1509900288,6432833536,-18893160448,40891670528,-63012511744,63209676800,-32678797312]),(⟨6,0,1⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨6,0,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,1,0⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨6,1,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,2,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,3,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨7,0,1⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨7,1,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856])]


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
    (Poly.add (Poly.scale (K.ofRat r719) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 5 6).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r718*r718 : ℚ)=r719 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 5 6 r718 r718 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 5=6 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 5 6).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C106

#print axioms Coulomb8.Columns.C106.sound
