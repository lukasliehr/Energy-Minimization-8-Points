import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C127

def r0 : ℚ := { num := 32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -1294336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 3309568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -248119296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 250888192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -8458452992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 26646052864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -42115301376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -57571295232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 566765371392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -1778870616064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 470844506112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -3532180209664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 1020316467200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 2948042031104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -4689807310848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 2967755210752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -742769131520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 8375500800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -950272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 21528576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -269123584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 7323648, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -11003101184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 37099241472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -66646540288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := -41607479296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 39279329280, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -128097353728, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 235722932224, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -4098536423424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 779873550336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 3911428636672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -5355709038592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 398967275520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -7838924800, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 327680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -34160640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 280690688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -1333411840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 3028516864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 3369222144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -48448700416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 160993460224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -244394098688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -20014350336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 838028623872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -1602467774464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := 1130510647296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 478173315072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -1287981400064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 84940308480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 1933312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -40337408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 434798592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -2751102976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 210534400, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -18280185856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := -3261693952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := 234357161984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -681437921280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 1056691027968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := -40773255168, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -520480325632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 1402814038016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -949329625088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 19107512320, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -49152, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 6045696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 17334272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := -523730944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := 3442786304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := -10519822336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := 8169390080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 54388817920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -225338933248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 58212564992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -321606615040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := -122818428928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := 65017397248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := -5495930880, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -983040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 18415616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -23068672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 722747392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -1287651328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -2625110016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 20249837568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -50088329216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := 1183645696, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -1785266176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -81402265600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := 78503919616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -1496973312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -163840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 4947968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := -7962624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := 301694976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -712835072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -519110656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 8215527424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -23707582464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := 31670108160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -1231126528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := -30493409280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 4260003840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -294912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 10813440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -24444928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 1555529728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -8973025280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 33366081536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := -71859175424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := 24710512640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 400391438336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -1489519181824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 398196670464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -2698951229440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 19453870080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 174595768320, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -67511648256, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := 25718128640, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := 933888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := -18825216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 192708608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -1121927168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := 3574743040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := -3041083392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -24448761856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 120933269504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -272502964224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 302011400192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := 674070528, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := -501009072128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 82860654592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -20994867200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := -2100264960, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := 49152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -1654784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := 22740992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := -1181155328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := 5078794240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := -11388567552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 106692608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := 4981522432, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := -279476322304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := 448024788992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := -284522250240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -228611915776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 75165155328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := -5669601280, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := -655360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := 15859712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -157941760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 851050496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -2645819392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 4125360128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 191102976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -2976120832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 40374239232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -20683554816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := -632422400, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := 42074112, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := -131072, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 30801920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := -220528640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := 824901632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -1000931328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := -4480565248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := 23792058368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -51050512384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 50982551552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 11456610304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -13777174528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 13667860480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -3397844992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := 35389440, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 98304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := 2883584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := -34373632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 81575936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 660930560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -110493696, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 17932419072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -32915767296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 31336136704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := 670957568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := -56350375936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 55728291840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -1095892992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 32768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -5996544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 64716800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -53248000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 1187971072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -1658781696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -1634009088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 10358685696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -14627799040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 36864000, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := 2084208640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -12943360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -1048576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 13467648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -88211456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := 297074688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -342884352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -848625664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 3088842752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -314998784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -414187520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 581206016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := -655360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := -327680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := 7274496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -62128128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 250347520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := -387317760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -464388096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 2451308544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -2263089152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := -1498218496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := 21037056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -2097152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := 17956864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := -142082048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := 950272000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -4355784704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := 13163036672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -26697793536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 34084618240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -1946157056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -1871052800, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 5439488000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := 196608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -38731776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 469893120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -3264872448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := 14318764032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -5694750720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := 59996110848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 12091392000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := -16511729664, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := 621436403712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := -78358118400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -23414046720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 15145697280, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := -543621120, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 31588352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -34996224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := 1135542272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -3109027840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := 547618816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := 4771807232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := -28646113280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := 6609305600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := -1590820864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := -8279425024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := 1206976512, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -9175040, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := 3997696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := -49610752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := 317128704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := -1024524288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 655884288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := 7688028160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := -31463178240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := 50612404224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := -52101120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := -150870753280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := 274222743552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := -28582019072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := 46530560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := 360448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := -37978112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 291274752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -1191346176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := 120389632, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := 3066101760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := -23340449792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := 45918060544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -13665271808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := -14859796480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := 27472003072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := -139100160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -3407872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 32374784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -124125184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := 23330816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := 10485760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -217317376, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := 3431727104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := 4881776640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := -19337576448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := 2892627968, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -3538944, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 24182784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := -16777216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := 7471104, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 975175680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -3995467776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 5003804672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := 4534894592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := -3250585600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := 26542080, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -6815744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 9699328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -18874368, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 661127168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 13631488, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := -647495680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := 10022289408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := -359923712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := -27787264, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := -3145728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := 1572864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -84934656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := -26476544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := 657457152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := -765984768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := -9437184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := -196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := 983040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := -95944704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := 679673856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := -2455830528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := 2575958016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 14174650368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -65119322112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 106678124544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := 2887581696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := -45353533440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := 10880483328, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := -378470400, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := 196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := -4980736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 2686976, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -164757504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := -24248320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := 1884291072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := -4928176128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := 544473088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := 1206845440, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := -30175133696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := -2558328832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := 57540608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := 14548992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := -124256256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := 500695040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -774635520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := -928776192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := 4902617088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := -4526178304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := -2996436992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := 42074112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := -6291456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := 3145728, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := -169869312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -52953088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := 1314914304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := -1531969536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := -18874368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := -647168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := 1654784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := -124059648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := 125444096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := -4229226496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := 13323026432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := -21057650688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := -28785647616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := 283382685696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := -889435308032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := 235422253056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := -1766090104832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := 510158233600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := 1474021015552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := -2344903655424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := 1483877605376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := -371384565760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := 4187750400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := 8192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := -475136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := 10764288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := -134561792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := 3661824, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := -5501550592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := 18549620736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := -33323270144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := -20803739648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := 19639664640, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := -64048676864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := 117861466112, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := -2049268211712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := 389936775168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := 1955714318336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := -2677854519296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := 199483637760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := -3919462400, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := 163840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := -17080320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := 140345344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := -666705920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := 1514258432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := 1684611072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := -24224350208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := 80496730112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := -122197049344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := -10007175168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := 419014311936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := -801233887232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := 565255323648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := 239086657536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := -643990700032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := 42470154240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := 966656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := -20168704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := 217399296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := -1375551488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := 105267200, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := -9140092928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := -1630846976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := 117178580992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := -340718960640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := 528345513984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := -20386627584, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := -260240162816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := 701407019008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := -474664812544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := 9553756160, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := -24576, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := 3022848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := 8667136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := -261865472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := 1721393152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := -5259911168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := 4084695040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := 27194408960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := -112669466624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := 29106282496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := -160803307520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := -61409214464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := 32508698624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := -2747965440, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := -491520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := 9207808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := -11534336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r454 : ℚ := { num := 361373696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r455 : ℚ := { num := -643825664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r456 : ℚ := { num := -1312555008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r457 : ℚ := { num := 10124918784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r458 : ℚ := { num := -25044164608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r459 : ℚ := { num := 591822848, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r460 : ℚ := { num := -892633088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r461 : ℚ := { num := -40701132800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r462 : ℚ := { num := 39251959808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r463 : ℚ := { num := -748486656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r464 : ℚ := { num := -81920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r465 : ℚ := { num := 2473984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r466 : ℚ := { num := -3981312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r467 : ℚ := { num := 150847488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r468 : ℚ := { num := -356417536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r469 : ℚ := { num := -259555328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r470 : ℚ := { num := 4107763712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r471 : ℚ := { num := -11853791232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r472 : ℚ := { num := 15835054080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r473 : ℚ := { num := -615563264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r474 : ℚ := { num := -15246704640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r475 : ℚ := { num := 2130001920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r476 : ℚ := { num := -147456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r477 : ℚ := { num := 5406720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r478 : ℚ := { num := -12222464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r479 : ℚ := { num := 777764864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r480 : ℚ := { num := -4486512640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r481 : ℚ := { num := 16683040768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r482 : ℚ := { num := -35929587712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r483 : ℚ := { num := 12355256320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r484 : ℚ := { num := 200195719168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r485 : ℚ := { num := -744759590912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r486 : ℚ := { num := 199098335232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r487 : ℚ := { num := -1349475614720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r488 : ℚ := { num := 9726935040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r489 : ℚ := { num := 87297884160, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r490 : ℚ := { num := -33755824128, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r491 : ℚ := { num := 12859064320, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r492 : ℚ := { num := -8192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r493 : ℚ := { num := 466944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r494 : ℚ := { num := -9412608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r495 : ℚ := { num := 96354304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r496 : ℚ := { num := -560963584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r497 : ℚ := { num := 1787371520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r498 : ℚ := { num := -1520541696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r499 : ℚ := { num := -12224380928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r500 : ℚ := { num := 60466634752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r501 : ℚ := { num := -136251482112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r502 : ℚ := { num := 151005700096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r503 : ℚ := { num := 337035264, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r504 : ℚ := { num := -250504536064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r505 : ℚ := { num := 41430327296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r506 : ℚ := { num := -10497433600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r507 : ℚ := { num := -1050132480, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r508 : ℚ := { num := 24576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r509 : ℚ := { num := -827392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r510 : ℚ := { num := 11370496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r511 : ℚ := { num := -590577664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r512 : ℚ := { num := 2539397120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r513 : ℚ := { num := -5694283776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r514 : ℚ := { num := 53346304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r515 : ℚ := { num := 2490761216, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r516 : ℚ := { num := -139738161152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r517 : ℚ := { num := 224012394496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r518 : ℚ := { num := -142261125120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r519 : ℚ := { num := -114305957888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r520 : ℚ := { num := 37582577664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r521 : ℚ := { num := -2834800640, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r522 : ℚ := { num := 7929856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r523 : ℚ := { num := -78970880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r524 : ℚ := { num := 425525248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r525 : ℚ := { num := -1322909696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r526 : ℚ := { num := 2062680064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r527 : ℚ := { num := 95551488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r528 : ℚ := { num := -1488060416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r529 : ℚ := { num := 20187119616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r530 : ℚ := { num := -10341777408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r531 : ℚ := { num := -316211200, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r532 : ℚ := { num := 21037056, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r533 : ℚ := { num := -65536, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r534 : ℚ := { num := 15400960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r535 : ℚ := { num := -110264320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r536 : ℚ := { num := 412450816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r537 : ℚ := { num := -500465664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r538 : ℚ := { num := -2240282624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r539 : ℚ := { num := 11896029184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r540 : ℚ := { num := -25525256192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r541 : ℚ := { num := 25491275776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r542 : ℚ := { num := 5728305152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r543 : ℚ := { num := -6888587264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r544 : ℚ := { num := 6833930240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r545 : ℚ := { num := -1698922496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r546 : ℚ := { num := 17694720, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r547 : ℚ := { num := 49152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r548 : ℚ := { num := 1441792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r549 : ℚ := { num := -17186816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r550 : ℚ := { num := 40787968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r551 : ℚ := { num := 330465280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r552 : ℚ := { num := -55246848, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r553 : ℚ := { num := 8966209536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r554 : ℚ := { num := -16457883648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r555 : ℚ := { num := 15668068352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r556 : ℚ := { num := 335478784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r557 : ℚ := { num := -28175187968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r558 : ℚ := { num := 27864145920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r559 : ℚ := { num := -547946496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r560 : ℚ := { num := 16384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r561 : ℚ := { num := -2998272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r562 : ℚ := { num := 32358400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r563 : ℚ := { num := -26624000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r564 : ℚ := { num := 593985536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r565 : ℚ := { num := -829390848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r566 : ℚ := { num := -817004544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r567 : ℚ := { num := 5179342848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r568 : ℚ := { num := -7313899520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r569 : ℚ := { num := 18432000, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r570 : ℚ := { num := 1042104320, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r571 : ℚ := { num := -6471680, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r572 : ℚ := { num := -524288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r573 : ℚ := { num := 6733824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r574 : ℚ := { num := -44105728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r575 : ℚ := { num := 148537344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r576 : ℚ := { num := -171442176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r577 : ℚ := { num := -424312832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r578 : ℚ := { num := 1544421376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r579 : ℚ := { num := -157499392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r580 : ℚ := { num := -207093760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r581 : ℚ := { num := 290603008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r582 : ℚ := { num := -327680, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r583 : ℚ := { num := 3637248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r584 : ℚ := { num := -31064064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r585 : ℚ := { num := 125173760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r586 : ℚ := { num := -193658880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r587 : ℚ := { num := -232194048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r588 : ℚ := { num := 1225654272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r589 : ℚ := { num := -1131544576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r590 : ℚ := { num := -749109248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r591 : ℚ := { num := 10518528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r592 : ℚ := { num := 8978432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r593 : ℚ := { num := -71041024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r594 : ℚ := { num := 475136000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r595 : ℚ := { num := -2177892352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r596 : ℚ := { num := 6581518336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r597 : ℚ := { num := -13348896768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r598 : ℚ := { num := 17042309120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r599 : ℚ := { num := -973078528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r600 : ℚ := { num := -935526400, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r601 : ℚ := { num := 2719744000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r602 : ℚ := { num := 98304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r603 : ℚ := { num := -19365888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r604 : ℚ := { num := 234946560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r605 : ℚ := { num := -1632436224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r606 : ℚ := { num := 7159382016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r607 : ℚ := { num := -2847375360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r608 : ℚ := { num := 29998055424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r609 : ℚ := { num := 6045696000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r610 : ℚ := { num := -8255864832, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r611 : ℚ := { num := 310718201856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r612 : ℚ := { num := -39179059200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r613 : ℚ := { num := -11707023360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r614 : ℚ := { num := 7572848640, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r615 : ℚ := { num := -271810560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r616 : ℚ := { num := 15794176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r617 : ℚ := { num := -17498112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r618 : ℚ := { num := 567771136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r619 : ℚ := { num := -1554513920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r620 : ℚ := { num := 273809408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r621 : ℚ := { num := 2385903616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r622 : ℚ := { num := -14323056640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r623 : ℚ := { num := 3304652800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r624 : ℚ := { num := -795410432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r625 : ℚ := { num := -4139712512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r626 : ℚ := { num := 603488256, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r627 : ℚ := { num := -4587520, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r628 : ℚ := { num := 1998848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r629 : ℚ := { num := -24805376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r630 : ℚ := { num := 158564352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r631 : ℚ := { num := -512262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r632 : ℚ := { num := 327942144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r633 : ℚ := { num := 3844014080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r634 : ℚ := { num := -15731589120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r635 : ℚ := { num := 25306202112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r636 : ℚ := { num := -26050560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r637 : ℚ := { num := -75435376640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r638 : ℚ := { num := 137111371776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r639 : ℚ := { num := -14291009536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r640 : ℚ := { num := 23265280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r641 : ℚ := { num := 180224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r642 : ℚ := { num := -18989056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r643 : ℚ := { num := 145637376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r644 : ℚ := { num := -595673088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r645 : ℚ := { num := 60194816, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r646 : ℚ := { num := 1533050880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r647 : ℚ := { num := -11670224896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r648 : ℚ := { num := 22959030272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r649 : ℚ := { num := -6832635904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r650 : ℚ := { num := -7429898240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r651 : ℚ := { num := 13736001536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r652 : ℚ := { num := -69550080, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r653 : ℚ := { num := -1703936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r654 : ℚ := { num := 16187392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r655 : ℚ := { num := -62062592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r656 : ℚ := { num := 11665408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r657 : ℚ := { num := 5242880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r658 : ℚ := { num := -108658688, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r659 : ℚ := { num := 1715863552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r660 : ℚ := { num := 2440888320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r661 : ℚ := { num := -9668788224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r662 : ℚ := { num := 1446313984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r663 : ℚ := { num := -1769472, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r664 : ℚ := { num := 12091392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r665 : ℚ := { num := -8388608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r666 : ℚ := { num := 3735552, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r667 : ℚ := { num := 487587840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r668 : ℚ := { num := -1997733888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r669 : ℚ := { num := 2501902336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r670 : ℚ := { num := 2267447296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r671 : ℚ := { num := -1625292800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r672 : ℚ := { num := 13271040, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r673 : ℚ := { num := 4849664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r674 : ℚ := { num := -9437184, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r675 : ℚ := { num := 330563584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r676 : ℚ := { num := 6815744, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r677 : ℚ := { num := -323747840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r678 : ℚ := { num := 5011144704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r679 : ℚ := { num := -179961856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r680 : ℚ := { num := -13893632, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r681 : ℚ := { num := -1572864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r682 : ℚ := { num := 786432, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r683 : ℚ := { num := -42467328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r684 : ℚ := { num := -13238272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r685 : ℚ := { num := 328728576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r686 : ℚ := { num := -382992384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r687 : ℚ := { num := -4718592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r688 : ℚ := { num := -98304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r689 : ℚ := { num := 491520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r690 : ℚ := { num := -47972352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r691 : ℚ := { num := 339836928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r692 : ℚ := { num := -1227915264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r693 : ℚ := { num := 1287979008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r694 : ℚ := { num := 7087325184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r695 : ℚ := { num := -32559661056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r696 : ℚ := { num := 53339062272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r697 : ℚ := { num := 1443790848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r698 : ℚ := { num := -22676766720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r699 : ℚ := { num := 5440241664, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r700 : ℚ := { num := -189235200, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r701 : ℚ := { num := -2490368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r702 : ℚ := { num := 1343488, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r703 : ℚ := { num := -82378752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r704 : ℚ := { num := -12124160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r705 : ℚ := { num := 942145536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r706 : ℚ := { num := -2464088064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r707 : ℚ := { num := 272236544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r708 : ℚ := { num := 603422720, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r709 : ℚ := { num := -15087566848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r710 : ℚ := { num := -1279164416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r711 : ℚ := { num := 28770304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r712 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r713 : ℚ := { num := 1, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18],[r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36],[r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53],[r54,r55,r56,r57,r58,r59,r60,r61,r62,r63,r64,r65,r66,r67,r68,r69],[r0,r70,r71,r72,r73,r74,r75,r76,r77,r78,r79,r80,r81,r82,r83],[r19,r84,r85,r86,r87,r88,r89,r90,r91,r92,r93,r94,r95,r96],[0,r97,r98,r99,r100,r101,r102,r103,r104,r105,r106,r107,r108],[],[],[],[],[],[],[0,r109,r110,r111,r112,r113,r114,r115,r116,r117,r118,r119,r120,r121,r122,r123,r124],[r125,r126,r127,r128,r129,r130,r131,r132,r133,r134,r135,r136,r137,r138,r139,r140],[0,r141,r142,r143,r144,r145,r146,r147,r148,r149,r150,r151,r152,r153,r154],[0,0,r155,r156,r157,r158,r159,r160,r161,r162,r163,r164,r165,r166],[],[],[],[],[],[],[],[r167,r168,r169,r170,r171,r172,r173,r174,r175,r176,r177,r178,r179,r180,r181],[r125,r182,r183,r184,r185,r186,r187,r188,r189,r190,r191,r192,r193,r194],[0,r195,r196,r197,r198,r199,r200,r201,r202,r203,r204,r205,r206],[r0,r207,r208,r209,r210,r211,r212,r213,r214,r215,r216,r217],[0,r218,r219,r220,r221,r222,r223,r224,r225,r226,r227],[],[],[],[],[0,r228,r229,r230,r231,r232,r233,r234,r235,r236,r237,r238,r239],[r0,r207,r208,r209,r210,r211,r212,r213,r214,r215,r216,r217],[0,r218,r219,r220,r221,r222,r223,r224,r225,r226,r227],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,0,r240,r241,r242,r243,r244,r245,r246,r247,r248,r249,r250,r251,r252,r253],[0,r167,r168,r254,r255,r256,r257,r258,r259,r260,r261,r262,r263,r264,r265],[0,0,r155,r156,r157,r158,r159,r160,r161,r162,r163,r164,r165,r166],[],[],[],[],[],[],[],[r266,r267,r268,r269,r270,r271,r272,r273,r274,r275,r276,r277,r278,r279],[r37,r280,r281,r282,r283,r284,r285,r286,r287,r288,r289,r290,r291],[r228,r292,r293,r294,r295,r296,r297,r298,r299,r300,r301,r302],[r167,r229,r303,r304,r305,r306,r307,r308,r309,r310,r311],[],[],[],[],[0,r312,r313,r314,r315,r316,r317,r318,r319,r320,r321,1835008],[],[],[],[],[],[],[r228,r322,r323,r324,r325,r326,r327,r328,131072],[],[],[],[],[r329,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340,r341],[r342,r343,r344,r345,r346,r347,r348,r349,r350,r351,r352,r353],[r167,r229,r303,r304,r305,r306,r307,r308,r309,r310,r311],[],[],[],[],[0,r155,r354,r355,r356,r357,r358,r359,r360,r361,r362],[],[r228,r322,r323,r324,r325,r326,r327,r328,131072],[],[],[r312,r363,r364,r365,r366,r367,r368,r369,262144],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[r19,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382,r383,r384,r385,r386,r387]),(⟨0,0,1⟩,[r388,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398,r399,r400,r401,r402,r403,r404,r405]),(⟨0,0,2⟩,[r54,r406,r407,r408,r409,r410,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420,r421]),(⟨0,0,3⟩,[r125,r422,r423,r424,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434,r435,r436]),(⟨0,0,4⟩,[r19,r437,r438,r439,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450]),(⟨0,0,5⟩,[r388,r451,r452,r453,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463]),(⟨0,0,6⟩,[0,r464,r465,r466,r467,r468,r469,r470,r471,r472,r473,r474,r475]),(⟨0,1,0⟩,[r388,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398,r399,r400,r401,r402,r403,r404,r405]),(⟨0,1,1⟩,[0,r476,r477,r478,r479,r480,r481,r482,r483,r484,r485,r486,r487,r488,r489,r490,r491]),(⟨0,1,2⟩,[r492,r493,r494,r495,r496,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506,r507]),(⟨0,1,3⟩,[0,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518,r519,r520,r521]),(⟨0,1,4⟩,[0,0,r218,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531,r532]),(⟨0,2,0⟩,[r54,r406,r407,r408,r409,r410,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420,r421]),(⟨0,2,1⟩,[r492,r493,r494,r495,r496,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506,r507]),(⟨0,2,2⟩,[r0,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543,r544,r545,r546]),(⟨0,2,3⟩,[r492,r547,r548,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558,r559]),(⟨0,2,4⟩,[0,r560,r561,r562,r563,r564,r565,r566,r567,r568,r569,r570,r571]),(⟨0,2,5⟩,[r19,r572,r573,r574,r575,r576,r577,r578,r579,r580,r581,r582]),(⟨0,2,6⟩,[0,r97,r583,r584,r585,r586,r587,r588,r589,r590,r591]),(⟨0,3,0⟩,[r125,r422,r423,r424,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434,r435,r436]),(⟨0,3,1⟩,[0,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518,r519,r520,r521]),(⟨0,3,2⟩,[r492,r547,r548,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558,r559]),(⟨0,3,3⟩,[0,r167,r207,r592,r593,r594,r595,r596,r597,r598,r599,r600,r601]),(⟨0,3,4⟩,[r19,r572,r573,r574,r575,r576,r577,r578,r579,r580,r581,r582]),(⟨0,3,5⟩,[0,r97,r583,r584,r585,r586,r587,r588,r589,r590,r591]),(⟨0,4,0⟩,[r19,r437,r438,r439,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450]),(⟨0,4,1⟩,[0,0,r218,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531,r532]),(⟨0,4,2⟩,[0,r560,r561,r562,r563,r564,r565,r566,r567,r568,r569,r570,r571]),(⟨0,4,3⟩,[r19,r572,r573,r574,r575,r576,r577,r578,r579,r580,r581,r582]),(⟨0,5,0⟩,[r388,r451,r452,r453,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463]),(⟨0,5,2⟩,[r19,r572,r573,r574,r575,r576,r577,r578,r579,r580,r581,r582]),(⟨0,5,3⟩,[0,r97,r583,r584,r585,r586,r587,r588,r589,r590,r591]),(⟨0,6,0⟩,[0,r464,r465,r466,r467,r468,r469,r470,r471,r472,r473,r474,r475]),(⟨0,6,2⟩,[0,r97,r583,r584,r585,r586,r587,r588,r589,r590,r591]),(⟨1,0,0⟩,[r388,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398,r399,r400,r401,r402,r403,r404,r405]),(⟨1,0,1⟩,[0,r476,r477,r478,r479,r480,r481,r482,r483,r484,r485,r486,r487,r488,r489,r490,r491]),(⟨1,0,2⟩,[r492,r493,r494,r495,r496,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506,r507]),(⟨1,0,3⟩,[0,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518,r519,r520,r521]),(⟨1,0,4⟩,[0,0,r218,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531,r532]),(⟨1,1,0⟩,[0,r476,r477,r478,r479,r480,r481,r482,r483,r484,r485,r486,r487,r488,r489,r490,r491]),(⟨1,1,1⟩,[0,0,r602,r603,r604,r605,r606,r607,r608,r609,r610,r611,r612,r613,r614,r615]),(⟨1,1,2⟩,[0,r0,r533,r616,r617,r618,r619,r620,r621,r622,r623,r624,r625,r626,r627]),(⟨1,1,3⟩,[0,0,r218,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531,r532]),(⟨1,2,0⟩,[r492,r493,r494,r495,r496,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506,r507]),(⟨1,2,1⟩,[0,r0,r533,r616,r617,r618,r619,r620,r621,r622,r623,r624,r625,r626,r627]),(⟨1,2,2⟩,[r37,r628,r629,r630,r631,r632,r633,r634,r635,r636,r637,r638,r639,r640]),(⟨1,2,3⟩,[r54,r641,r642,r643,r644,r645,r646,r647,r648,r649,r650,r651,r652]),(⟨1,2,4⟩,[r167,r653,r654,r655,r656,r657,r658,r659,r660,r661,r662,r663]),(⟨1,2,5⟩,[r0,r207,r664,r665,r666,r667,r668,r669,r670,r671,r672]),(⟨1,3,0⟩,[0,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518,r519,r520,r521]),(⟨1,3,1⟩,[0,0,r218,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531,r532]),(⟨1,3,2⟩,[r54,r641,r642,r643,r644,r645,r646,r647,r648,r649,r650,r651,r652]),(⟨1,3,3⟩,[0,r228,r292,r673,r674,r675,r676,r677,r678,r679,r680,917504]),(⟨1,4,0⟩,[0,0,r218,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531,r532]),(⟨1,4,2⟩,[r167,r653,r654,r655,r656,r657,r658,r659,r660,r661,r662,r663]),(⟨1,4,5⟩,[r167,r681,r682,r683,r684,r685,r686,r687,65536]),(⟨1,5,2⟩,[r0,r207,r664,r665,r666,r667,r668,r669,r670,r671,r672]),(⟨1,5,4⟩,[r167,r681,r682,r683,r684,r685,r686,r687,65536]),(⟨2,0,0⟩,[r54,r406,r407,r408,r409,r410,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420,r421]),(⟨2,0,1⟩,[r492,r493,r494,r495,r496,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506,r507]),(⟨2,0,2⟩,[r0,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543,r544,r545,r546]),(⟨2,0,3⟩,[r492,r547,r548,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558,r559]),(⟨2,0,4⟩,[0,r560,r561,r562,r563,r564,r565,r566,r567,r568,r569,r570,r571]),(⟨2,0,5⟩,[r19,r572,r573,r574,r575,r576,r577,r578,r579,r580,r581,r582]),(⟨2,0,6⟩,[0,r97,r583,r584,r585,r586,r587,r588,r589,r590,r591]),(⟨2,1,0⟩,[r492,r493,r494,r495,r496,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506,r507]),(⟨2,1,1⟩,[0,r0,r533,r616,r617,r618,r619,r620,r621,r622,r623,r624,r625,r626,r627]),(⟨2,1,2⟩,[r37,r628,r629,r630,r631,r632,r633,r634,r635,r636,r637,r638,r639,r640]),(⟨2,1,3⟩,[r54,r641,r642,r643,r644,r645,r646,r647,r648,r649,r650,r651,r652]),(⟨2,1,4⟩,[r167,r653,r654,r655,r656,r657,r658,r659,r660,r661,r662,r663]),(⟨2,1,5⟩,[r0,r207,r664,r665,r666,r667,r668,r669,r670,r671,r672]),(⟨2,2,0⟩,[r0,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543,r544,r545,r546]),(⟨2,2,1⟩,[r37,r628,r629,r630,r631,r632,r633,r634,r635,r636,r637,r638,r639,r640]),(⟨2,2,2⟩,[r688,r689,r690,r691,r692,r693,r694,r695,r696,r697,r698,r699,r700]),(⟨2,2,3⟩,[r182,r701,r702,r703,r704,r705,r706,r707,r708,r709,r710,r711]),(⟨2,2,4⟩,[r0,r207,r664,r665,r666,r667,r668,r669,r670,r671,r672]),(⟨2,3,0⟩,[r492,r547,r548,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558,r559]),(⟨2,3,1⟩,[r54,r641,r642,r643,r644,r645,r646,r647,r648,r649,r650,r651,r652]),(⟨2,3,2⟩,[r182,r701,r702,r703,r704,r705,r706,r707,r708,r709,r710,r711]),(⟨2,3,3⟩,[0,r218,r219,r220,r221,r222,r223,r224,r225,r226,r227]),(⟨2,3,5⟩,[r167,r681,r682,r683,r684,r685,r686,r687,65536]),(⟨2,4,0⟩,[0,r560,r561,r562,r563,r564,r565,r566,r567,r568,r569,r570,r571]),(⟨2,4,1⟩,[r167,r653,r654,r655,r656,r657,r658,r659,r660,r661,r662,r663]),(⟨2,4,2⟩,[r0,r207,r664,r665,r666,r667,r668,r669,r670,r671,r672]),(⟨2,4,4⟩,[r228,r322,r323,r324,r325,r326,r327,r328,131072]),(⟨2,5,0⟩,[r19,r572,r573,r574,r575,r576,r577,r578,r579,r580,r581,r582]),(⟨2,5,1⟩,[r0,r207,r664,r665,r666,r667,r668,r669,r670,r671,r672]),(⟨2,5,3⟩,[r167,r681,r682,r683,r684,r685,r686,r687,65536]),(⟨2,6,0⟩,[0,r97,r583,r584,r585,r586,r587,r588,r589,r590,r591]),(⟨3,0,0⟩,[r125,r422,r423,r424,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434,r435,r436]),(⟨3,0,1⟩,[0,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518,r519,r520,r521]),(⟨3,0,2⟩,[r492,r547,r548,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558,r559]),(⟨3,0,3⟩,[0,r167,r207,r592,r593,r594,r595,r596,r597,r598,r599,r600,r601]),(⟨3,0,4⟩,[r19,r572,r573,r574,r575,r576,r577,r578,r579,r580,r581,r582]),(⟨3,0,5⟩,[0,r97,r583,r584,r585,r586,r587,r588,r589,r590,r591]),(⟨3,1,0⟩,[0,r508,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518,r519,r520,r521]),(⟨3,1,1⟩,[0,0,r218,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531,r532]),(⟨3,1,2⟩,[r54,r641,r642,r643,r644,r645,r646,r647,r648,r649,r650,r651,r652]),(⟨3,1,3⟩,[0,r228,r292,r673,r674,r675,r676,r677,r678,r679,r680,917504]),(⟨3,2,0⟩,[r492,r547,r548,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558,r559]),(⟨3,2,1⟩,[r54,r641,r642,r643,r644,r645,r646,r647,r648,r649,r650,r651,r652]),(⟨3,2,2⟩,[r182,r701,r702,r703,r704,r705,r706,r707,r708,r709,r710,r711]),(⟨3,2,3⟩,[0,r218,r219,r220,r221,r222,r223,r224,r225,r226,r227]),(⟨3,2,5⟩,[r167,r681,r682,r683,r684,r685,r686,r687,65536]),(⟨3,3,0⟩,[0,r167,r207,r592,r593,r594,r595,r596,r597,r598,r599,r600,r601]),(⟨3,3,1⟩,[0,r228,r292,r673,r674,r675,r676,r677,r678,r679,r680,917504]),(⟨3,3,2⟩,[0,r218,r219,r220,r221,r222,r223,r224,r225,r226,r227]),(⟨3,4,0⟩,[r19,r572,r573,r574,r575,r576,r577,r578,r579,r580,r581,r582]),(⟨3,5,0⟩,[0,r97,r583,r584,r585,r586,r587,r588,r589,r590,r591]),(⟨3,5,2⟩,[r167,r681,r682,r683,r684,r685,r686,r687,65536]),(⟨4,0,0⟩,[r19,r437,r438,r439,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450]),(⟨4,0,1⟩,[0,0,r218,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531,r532]),(⟨4,0,2⟩,[0,r560,r561,r562,r563,r564,r565,r566,r567,r568,r569,r570,r571]),(⟨4,0,3⟩,[r19,r572,r573,r574,r575,r576,r577,r578,r579,r580,r581,r582]),(⟨4,1,0⟩,[0,0,r218,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531,r532]),(⟨4,1,2⟩,[r167,r653,r654,r655,r656,r657,r658,r659,r660,r661,r662,r663]),(⟨4,1,5⟩,[r167,r681,r682,r683,r684,r685,r686,r687,65536]),(⟨4,2,0⟩,[0,r560,r561,r562,r563,r564,r565,r566,r567,r568,r569,r570,r571]),(⟨4,2,1⟩,[r167,r653,r654,r655,r656,r657,r658,r659,r660,r661,r662,r663]),(⟨4,2,2⟩,[r0,r207,r664,r665,r666,r667,r668,r669,r670,r671,r672]),(⟨4,2,4⟩,[r228,r322,r323,r324,r325,r326,r327,r328,131072]),(⟨4,3,0⟩,[r19,r572,r573,r574,r575,r576,r577,r578,r579,r580,r581,r582]),(⟨4,4,2⟩,[r228,r322,r323,r324,r325,r326,r327,r328,131072]),(⟨4,5,1⟩,[r167,r681,r682,r683,r684,r685,r686,r687,65536]),(⟨5,0,0⟩,[r388,r451,r452,r453,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463]),(⟨5,0,2⟩,[r19,r572,r573,r574,r575,r576,r577,r578,r579,r580,r581,r582]),(⟨5,0,3⟩,[0,r97,r583,r584,r585,r586,r587,r588,r589,r590,r591]),(⟨5,1,2⟩,[r0,r207,r664,r665,r666,r667,r668,r669,r670,r671,r672]),(⟨5,1,4⟩,[r167,r681,r682,r683,r684,r685,r686,r687,65536]),(⟨5,2,0⟩,[r19,r572,r573,r574,r575,r576,r577,r578,r579,r580,r581,r582]),(⟨5,2,1⟩,[r0,r207,r664,r665,r666,r667,r668,r669,r670,r671,r672]),(⟨5,2,3⟩,[r167,r681,r682,r683,r684,r685,r686,r687,65536]),(⟨5,3,0⟩,[0,r97,r583,r584,r585,r586,r587,r588,r589,r590,r591]),(⟨5,3,2⟩,[r167,r681,r682,r683,r684,r685,r686,r687,65536]),(⟨5,4,1⟩,[r167,r681,r682,r683,r684,r685,r686,r687,65536]),(⟨6,0,0⟩,[0,r464,r465,r466,r467,r468,r469,r470,r471,r472,r473,r474,r475]),(⟨6,0,2⟩,[0,r97,r583,r584,r585,r586,r587,r588,r589,r590,r591]),(⟨6,2,0⟩,[0,r97,r583,r584,r585,r586,r587,r588,r589,r590,r591])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[128,-2368,16192,-48960,27712,296128,-1096256,1862976,-1545664,318080]),(⟨0,0,1⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨0,0,2⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨0,0,3⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨0,1,0⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨0,1,1⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248]),(⟨0,2,0⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨0,2,3⟩,[-128,1536,-3840,-4608,15232]),(⟨0,3,0⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨0,3,2⟩,[-128,1536,-3840,-4608,15232]),(⟨1,0,0⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨1,0,1⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248]),(⟨1,1,0⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248]),(⟨2,0,0⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨2,0,3⟩,[-128,1536,-3840,-4608,15232]),(⟨2,3,0⟩,[-128,1536,-3840,-4608,15232]),(⟨3,0,0⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨3,0,2⟩,[-128,1536,-3840,-4608,15232]),(⟨3,2,0⟩,[-128,1536,-3840,-4608,15232])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[128,-2688,24576,-125568,372480,-579456,211968,627840,-719744,92160]),(⟨0,0,1⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨0,0,2⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨0,0,3⟩,[0,1280,-13056,47616,-60928,-24320,82176]),(⟨0,1,0⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨0,2,0⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨0,3,0⟩,[0,1280,-13056,47616,-60928,-24320,82176]),(⟨1,0,0⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨1,2,2⟩,[-512,6144,-15360,-18432,60928]),(⟨2,0,0⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨2,1,2⟩,[-512,6144,-15360,-18432,60928]),(⟨2,2,1⟩,[-512,6144,-15360,-18432,60928]),(⟨3,0,0⟩,[0,1280,-13056,47616,-60928,-24320,82176])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 7 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r712) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 12 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r712) sourceRight))).isZero := by decide +kernel

noncomputable def partial19 : Poly := []

theorem partial_sound19 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 19)
      sourceRight).eval u v t=partial19.eval u v t := by rfl

noncomputable def chunk16 : Poly := [(⟨3,0,0⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨3,0,2⟩,[-128,1536,-3840,-4608,15232]),(⟨3,2,0⟩,[-128,1536,-3840,-4608,15232])]

noncomputable def partial16 : Poly := [(⟨3,0,0⟩,[-8192,335872,-5824512,56852480,-341647360,1239719936,-2000609280,-4280156160,35080675328,-101211676672,159393669120,-108466503680,-75079835648,212775854080,-142740725760,16721510400]),(⟨3,0,1⟩,[0,57344,-1957888,26624000,-191315968,766582784,-1352867840,-2300608512,20732346368,-59274485760,89946316800,-54880747520,-49287741440,114127462400,-64215244800]),(⟨3,0,2⟩,[-8192,212992,-2523136,20332544,-130129920,632946688,-2116681728,4495015936,-5479161856,2087665664,6458212352,-16193077248,14222303232,-1847623680]),(⟨3,0,3⟩,[0,32768,-524288,4489216,-35520512,237568000,-1088946176,3290759168,-6674448384,8521154560,-3405774848,-7951974400,9519104000]),(⟨3,0,4⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨3,0,5⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨3,1,0⟩,[0,57344,-1957888,26624000,-191315968,766582784,-1352867840,-2300608512,20732346368,-59274485760,89946316800,-54880747520,-49287741440,114127462400,-64215244800]),(⟨3,1,2⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨3,2,0⟩,[-8192,212992,-2523136,20332544,-130129920,632946688,-2116681728,4495015936,-5479161856,2087665664,6458212352,-16193077248,14222303232,-1847623680]),(⟨3,2,1⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨3,2,2⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨3,2,3⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨3,3,0⟩,[0,32768,-524288,4489216,-35520512,237568000,-1088946176,3290759168,-6674448384,8521154560,-3405774848,-7951974400,9519104000]),(⟨3,3,2⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨3,4,0⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨3,5,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨4,0,0⟩,[0,57344,-1957888,26624000,-191315968,766582784,-1352867840,-2300608512,20732346368,-59274485760,89946316800,-54880747520,-49287741440,114127462400,-64215244800]),(⟨4,0,2⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨4,2,0⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨4,2,2⟩,[32768,-1048576,12091392,-58720256,63504384,487587840,-1997733888,2501902336,2267447296,-11377049600,11054776320]),(⟨4,2,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,4,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,0,0⟩,[8192,-327680,5242880,-43220992,190455808,-341344256,-722141184,5653725184,-14065442816,15418916864,3217227776,-28719022080,25610117120,-3251404800]),(⟨5,0,2⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨5,1,2⟩,[32768,-1048576,12091392,-58720256,63504384,487587840,-1997733888,2501902336,2267447296,-11377049600,11054776320]),(⟨5,1,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,2,0⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨5,2,1⟩,[32768,-1048576,12091392,-58720256,63504384,487587840,-1997733888,2501902336,2267447296,-11377049600,11054776320]),(⟨5,2,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,3,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,4,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨6,0,0⟩,[0,-81920,2473984,-27869184,150847488,-356417536,-259555328,4107763712,-11853791232,15835054080,-4308942848,-15246704640,14910013440]),(⟨6,0,2⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨6,2,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832])]


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

noncomputable def partial12 : Poly := [(⟨1,1,0⟩,[0,-32768,1146880,-17924096,165740544,-1004109824,4120674304,-11174445056,16900816896,2283831296,-77229555712,180014907392,-174549565440,-27505623040,223722045440,-165044518912,19652935680]),(⟨1,1,1⟩,[0,0,229376,-6455296,78315520,-544145408,2386460672,-6643875840,9999351808,2015232000,-46783234048,103572733952,-91417804800,-27316387840,123689861120,-75472732160]),(⟨1,1,2⟩,[0,32768,-1114112,15794176,-122486784,567771136,-1554513920,1916665856,2385903616,-14323056640,23132569600,-5567873024,-28977987584,29570924544,-3821404160]),(⟨1,1,3⟩,[0,0,-327680,7929856,-78970880,425525248,-1322909696,2062680064,668860416,-10416422912,20187119616,-10341777408,-15494348800,17523867648]),(⟨1,2,0⟩,[0,0,229376,-6455296,78315520,-544145408,2386460672,-6643875840,9999351808,2015232000,-46783234048,103572733952,-91417804800,-27316387840,123689861120,-75472732160]),(⟨1,3,0⟩,[0,32768,-1114112,15794176,-122486784,567771136,-1554513920,1916665856,2385903616,-14323056640,23132569600,-5567873024,-28977987584,29570924544,-3821404160]),(⟨1,4,0⟩,[0,0,-327680,7929856,-78970880,425525248,-1322909696,2062680064,668860416,-10416422912,20187119616,-10341777408,-15494348800,17523867648]),(⟨2,0,0⟩,[-16384,573440,-8765440,76562432,-412188672,1308672000,-1505001472,-6487916544,37962170368,-97309147136,142530789376,-94421467136,-59892498432,182976135168,-140276989952,32051478528,-2229534720]),(⟨2,0,1⟩,[0,114688,-3227648,37781504,-237355008,819560448,-1046151168,-3676291072,22369697792,-56550178816,79980314624,-48055123968,-39128186880,98383953920,-65215037440,8562032640]),(⟨2,0,2⟩,[16384,-557056,7700480,-55132160,206225408,-250232832,-1120141312,5948014592,-12762628096,12745637888,2864152576,-24110055424,23918755840,-5946228736,433520640]),(⟨2,0,3⟩,[-16384,376832,-3801088,26034176,-149667840,671809536,-1984954368,3312484352,-2392440832,249151488,-868876288,543834112,2254028800,-584220672]),(⟨2,0,4⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨2,0,5⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨2,0,6⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨2,1,0⟩,[0,114688,-2998272,31326208,-159039488,275415040,1340309504,-10320166912,32369049600,-54534946816,33197080576,55517609984,-130545991680,71067566080,58474823680,-66910699520]),(⟨2,1,3⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨2,2,0⟩,[16384,-557056,7700480,-55132160,206225408,-250232832,-1120141312,5948014592,-12762628096,12745637888,2864152576,-24110055424,23918755840,-5946228736,433520640]),(⟨2,2,3⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨2,3,0⟩,[-16384,376832,-3801088,26034176,-149667840,671809536,-1984954368,3312484352,-2392440832,249151488,-868876288,543834112,2254028800,-584220672]),(⟨2,3,1⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨2,3,2⟩,[16384,-393216,3325952,-10158080,-11894784,159121408,-308445184,-721813504,3908648960,-2709389312,-9539174400,12719816704]),(⟨2,3,3⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨2,4,0⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨2,5,0⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨2,6,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨3,0,0⟩,[-8192,450560,-9052160,94633984,-579002368,2059280384,-3046760448,-7956447232,57450373120,-157761855488,239373983744,-156521627648,-114208022528,311159808000,-207955763200,25283543040]),(⟨3,0,1⟩,[0,57344,-1957888,26624000,-191315968,766582784,-1352867840,-2300608512,20732346368,-59274485760,89946316800,-54880747520,-49287741440,114127462400,-64215244800]),(⟨3,0,2⟩,[-8192,212992,-2523136,20332544,-130129920,632946688,-2116681728,4495015936,-5479161856,2087665664,6458212352,-16193077248,14222303232,-1847623680]),(⟨3,0,3⟩,[0,147456,-3522560,36847616,-221888512,831553536,-1918337024,2473754624,-1495105536,1207255040,-2502606848,-657244160,4128194560]),(⟨3,0,4⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨3,0,5⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨3,1,0⟩,[0,90112,-3072000,42418176,-313802752,1334353920,-2907381760,-383942656,23118249984,-73597542400,113078886400,-60448620544,-78265729024,143698386944,-68036648960]),(⟨3,1,2⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨3,2,0⟩,[-8192,212992,-2523136,20332544,-130129920,632946688,-2116681728,4495015936,-5479161856,2087665664,6458212352,-16193077248,14222303232,-1847623680]),(⟨3,2,1⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨3,2,2⟩,[98304,-2621440,26247168,-116326400,148307968,611581952,-2579955712,2538471424,5247041536,-13827833856,2619244544,10972889088]),(⟨3,2,3⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨3,2,5⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,3,0⟩,[0,147456,-3522560,36847616,-221888512,831553536,-1918337024,2473754624,-1495105536,1207255040,-2502606848,-657244160,4128194560]),(⟨3,3,1⟩,[0,131072,-3407872,33947648,-160432128,330563584,115867648,-2266234880,5011144704,-1259732992,-11573395456,12992774144]),(⟨3,3,2⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨3,4,0⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨3,5,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨3,5,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,0,0⟩,[16384,-499712,5742592,-28508160,14909440,516349952,-2473009152,3647406080,7969718272,-46528847872,92810469376,-78990802944,-25368985600,108181233664,-63781724160]),(⟨4,0,2⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨4,0,3⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨4,1,0⟩,[0,0,-327680,7929856,-78970880,425525248,-1322909696,2062680064,668860416,-10416422912,20187119616,-10341777408,-15494348800,17523867648]),(⟨4,1,2⟩,[65536,-1703936,16187392,-62062592,11665408,623902720,-1847197696,1715863552,2440888320,-9668788224,10124197888,-1473970176]),(⟨4,1,5⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,2,0⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨4,2,1⟩,[65536,-1703936,16187392,-62062592,11665408,623902720,-1847197696,1715863552,2440888320,-9668788224,10124197888,-1473970176]),(⟨4,2,2⟩,[32768,-1048576,12091392,-58720256,63504384,487587840,-1997733888,2501902336,2267447296,-11377049600,11054776320]),(⟨4,2,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,3,0⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨4,4,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,5,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,0,0⟩,[8192,-491520,9207808,-80740352,361373696,-643825664,-1312555008,10124918784,-25044164608,28999319552,-892633088,-40701132800,39251959808,-5239406592]),(⟨5,0,2⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨5,0,3⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨5,1,2⟩,[32768,-1048576,12091392,-58720256,63504384,487587840,-1997733888,2501902336,2267447296,-11377049600,11054776320]),(⟨5,1,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,2,0⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨5,2,1⟩,[32768,-1048576,12091392,-58720256,63504384,487587840,-1997733888,2501902336,2267447296,-11377049600,11054776320]),(⟨5,2,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,3,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨5,3,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,4,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨6,0,0⟩,[0,-81920,2473984,-27869184,150847488,-356417536,-259555328,4107763712,-11853791232,15835054080,-4308942848,-15246704640,14910013440]),(⟨6,0,2⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨6,2,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832])]


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

noncomputable def partial8 : Poly := [(⟨0,3,0⟩,[-8192,335872,-5824512,56852480,-341647360,1239719936,-2000609280,-4280156160,35080675328,-101211676672,159393669120,-108466503680,-75079835648,212775854080,-142740725760,16721510400]),(⟨0,3,1⟩,[0,57344,-1957888,26624000,-191315968,766582784,-1352867840,-2300608512,20732346368,-59274485760,89946316800,-54880747520,-49287741440,114127462400,-64215244800]),(⟨0,3,2⟩,[-8192,212992,-2523136,20332544,-130129920,632946688,-2116681728,4495015936,-5479161856,2087665664,6458212352,-16193077248,14222303232,-1847623680]),(⟨0,3,3⟩,[0,32768,-524288,4489216,-35520512,237568000,-1088946176,3290759168,-6674448384,8521154560,-3405774848,-7951974400,9519104000]),(⟨0,3,4⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨0,3,5⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨0,4,0⟩,[0,57344,-1957888,26624000,-191315968,766582784,-1352867840,-2300608512,20732346368,-59274485760,89946316800,-54880747520,-49287741440,114127462400,-64215244800]),(⟨0,4,2⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨0,5,0⟩,[8192,-327680,5242880,-43220992,190455808,-341344256,-722141184,5653725184,-14065442816,15418916864,3217227776,-28719022080,25610117120,-3251404800]),(⟨0,5,2⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨0,6,0⟩,[0,-81920,2473984,-27869184,150847488,-356417536,-259555328,4107763712,-11853791232,15835054080,-4308942848,-15246704640,14910013440]),(⟨0,6,2⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨1,0,0⟩,[8192,-360448,7020544,-80592896,605929472,-3093446656,10474053632,-19728236544,-5879316480,168439054336,-570073292800,1063007830016,-1085825171456,174493646848,1106226159616,-1470031036416,731069194240,-79478784000]),(⟨1,0,1⟩,[0,-90112,3276800,-51740672,471752704,-2745311232,10401857536,-23552016384,14628036608,101239775232,-410994573312,786851627008,-762012590080,20291461120,853893038080,-909539950592,324873543680]),(⟨1,0,2⟩,[-8192,352256,-6184960,58572800,-323608576,967811072,-474390528,-8548089856,38096936960,-79701303296,71025385472,53784723456,-211376349184,191628337152,-8266997760,-60018524160]),(⟨1,0,3⟩,[0,114688,-3833856,52969472,-399261696,1772814336,-4341415936,2353954816,21610594304,-80463675392,134066077696,-87380377600,-65018216448,148950581248,-74689986560]),(⟨1,0,4⟩,[0,0,-327680,7929856,-78970880,425525248,-1322909696,2062680064,668860416,-10416422912,20187119616,-10341777408,-15494348800,17523867648]),(⟨1,1,0⟩,[0,-90112,3276800,-51740672,471752704,-2745311232,10401857536,-23552016384,14628036608,101239775232,-410994573312,786851627008,-762012590080,20291461120,853893038080,-909539950592,324873543680]),(⟨1,1,1⟩,[0,0,458752,-12910592,156631040,-1088290816,4772921344,-13287751680,19998703616,4030464000,-93566468096,207145467904,-182835609600,-54632775680,247379722240,-150945464320]),(⟨1,1,2⟩,[0,32768,-1114112,15794176,-122486784,567771136,-1554513920,1916665856,2385903616,-14323056640,23132569600,-5567873024,-28977987584,29570924544,-3821404160]),(⟨1,1,3⟩,[0,0,-327680,7929856,-78970880,425525248,-1322909696,2062680064,668860416,-10416422912,20187119616,-10341777408,-15494348800,17523867648]),(⟨1,2,0⟩,[-8192,352256,-6184960,58572800,-323608576,967811072,-474390528,-8548089856,38096936960,-79701303296,71025385472,53784723456,-211376349184,191628337152,-8266997760,-60018524160]),(⟨1,2,1⟩,[0,32768,-1114112,15794176,-122486784,567771136,-1554513920,1916665856,2385903616,-14323056640,23132569600,-5567873024,-28977987584,29570924544,-3821404160]),(⟨1,3,0⟩,[0,172032,-5791744,79593472,-590577664,2539397120,-5694283776,53346304,42342940672,-139738161152,224012394496,-142261125120,-114305957888,263078043648,-138905231360]),(⟨1,3,1⟩,[0,0,-327680,7929856,-78970880,425525248,-1322909696,2062680064,668860416,-10416422912,20187119616,-10341777408,-15494348800,17523867648]),(⟨1,3,2⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨1,4,0⟩,[0,0,-327680,7929856,-78970880,425525248,-1322909696,2062680064,668860416,-10416422912,20187119616,-10341777408,-15494348800,17523867648]),(⟨1,5,2⟩,[32768,-1048576,12091392,-58720256,63504384,487587840,-1997733888,2501902336,2267447296,-11377049600,11054776320]),(⟨1,5,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,0,0⟩,[-16384,516096,-6635520,42745856,-106176512,-432529408,4776181760,-18865487872,35689390080,1646796800,-191234228224,512415252480,-647355523072,230773219328,489894002688,-712443953152,302991073280]),(⟨2,0,1⟩,[0,114688,-2998272,31326208,-159039488,275415040,1340309504,-10320166912,32369049600,-54534946816,33197080576,55517609984,-130545991680,71067566080,58474823680,-66910699520]),(⟨2,0,2⟩,[16384,-557056,7700480,-55132160,206225408,-250232832,-1120141312,5948014592,-12762628096,12745637888,2864152576,-24110055424,23918755840,-5946228736,433520640]),(⟨2,0,3⟩,[-16384,376832,-3801088,26034176,-149667840,671809536,-1984954368,3312484352,-2392440832,249151488,-868876288,543834112,2254028800,-584220672]),(⟨2,0,4⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨2,0,5⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨2,0,6⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨2,1,0⟩,[0,114688,-2998272,31326208,-159039488,275415040,1340309504,-10320166912,32369049600,-54534946816,33197080576,55517609984,-130545991680,71067566080,58474823680,-66910699520]),(⟨2,1,3⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨2,2,0⟩,[16384,-557056,7700480,-55132160,206225408,-250232832,-1120141312,5948014592,-12762628096,12745637888,2864152576,-24110055424,23918755840,-5946228736,433520640]),(⟨2,2,2⟩,[-32768,1146880,-15990784,113278976,-409305088,429326336,2362441728,-10853220352,17779687424,481263616,-52912455680,88857280512,-52544307200]),(⟨2,2,3⟩,[16384,-393216,3325952,-10158080,-11894784,159121408,-308445184,-721813504,3908648960,-2709389312,-9539174400,12719816704]),(⟨2,3,0⟩,[-8192,49152,1441792,-17186816,40787968,330465280,-2707095552,8966209536,-16457883648,15668068352,2348351488,-28175187968,27864145920,-3835625472]),(⟨2,3,1⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨2,3,2⟩,[32768,-917504,10059776,-54263808,136642560,-12320768,-732758016,822607872,2806153216,-4159045632,-7504953344,12446859264]),(⟨2,3,3⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨2,4,0⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨2,4,2⟩,[32768,-1048576,12091392,-58720256,63504384,487587840,-1997733888,2501902336,2267447296,-11377049600,11054776320]),(⟨2,4,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,5,0⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨2,5,1⟩,[32768,-1048576,12091392,-58720256,63504384,487587840,-1997733888,2501902336,2267447296,-11377049600,11054776320]),(⟨2,5,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,6,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨3,0,0⟩,[-16384,802816,-15466496,159662080,-980926464,3571236864,-5907611648,-9860661248,85547958272,-239478390784,357182603264,-206309638144,-234166566912,530104532992,-339912622080,40737751040]),(⟨3,0,1⟩,[0,90112,-3072000,42418176,-313802752,1334353920,-2907381760,-383942656,23118249984,-73597542400,113078886400,-60448620544,-78265729024,143698386944,-68036648960]),(⟨3,0,2⟩,[-8192,212992,-2523136,20332544,-130129920,632946688,-2116681728,4495015936,-5479161856,2087665664,6458212352,-16193077248,14222303232,-1847623680]),(⟨3,0,3⟩,[0,147456,-3522560,36847616,-221888512,831553536,-1918337024,2473754624,-1495105536,1207255040,-2502606848,-657244160,4128194560]),(⟨3,0,4⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨3,0,5⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨3,1,0⟩,[0,90112,-3072000,42418176,-313802752,1334353920,-2907381760,-383942656,23118249984,-73597542400,113078886400,-60448620544,-78265729024,143698386944,-68036648960]),(⟨3,1,2⟩,[-32768,1261568,-18989056,145637376,-595673088,1023311872,1533050880,-11670224896,22959030272,-6832635904,-52009287680,96152010752,-57935216640]),(⟨3,1,3⟩,[0,131072,-3407872,33947648,-160432128,330563584,115867648,-2266234880,5011144704,-1259732992,-11573395456,12992774144]),(⟨3,2,0⟩,[-8192,212992,-2523136,20332544,-130129920,632946688,-2116681728,4495015936,-5479161856,2087665664,6458212352,-16193077248,14222303232,-1847623680]),(⟨3,2,1⟩,[-32768,1261568,-18989056,145637376,-595673088,1023311872,1533050880,-11670224896,22959030272,-6832635904,-52009287680,96152010752,-57935216640]),(⟨3,2,2⟩,[98304,-2490368,22839296,-82378752,-12124160,942145536,-2464088064,272236544,10258186240,-15087566848,-8954150912,23965663232]),(⟨3,2,3⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨3,2,5⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,3,0⟩,[0,65536,-1048576,8978432,-71041024,475136000,-2177892352,6581518336,-13348896768,17042309120,-6811549696,-15903948800,19038208000]),(⟨3,3,1⟩,[0,131072,-3407872,33947648,-160432128,330563584,115867648,-2266234880,5011144704,-1259732992,-11573395456,12992774144]),(⟨3,3,2⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨3,4,0⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨3,5,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨3,5,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,0,0⟩,[16384,-417792,3022848,8667136,-261865472,1721393152,-5259911168,4084695040,27194408960,-112669466624,203743977472,-160803307520,-61409214464,227560890368,-134650306560]),(⟨4,0,1⟩,[0,0,-327680,7929856,-78970880,425525248,-1322909696,2062680064,668860416,-10416422912,20187119616,-10341777408,-15494348800,17523867648]),(⟨4,0,2⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨4,0,3⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨4,1,0⟩,[0,0,-327680,7929856,-78970880,425525248,-1322909696,2062680064,668860416,-10416422912,20187119616,-10341777408,-15494348800,17523867648]),(⟨4,1,2⟩,[65536,-1703936,16187392,-62062592,11665408,623902720,-1847197696,1715863552,2440888320,-9668788224,10124197888,-1473970176]),(⟨4,1,5⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,2,0⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨4,2,1⟩,[65536,-1703936,16187392,-62062592,11665408,623902720,-1847197696,1715863552,2440888320,-9668788224,10124197888,-1473970176]),(⟨4,2,2⟩,[32768,-1048576,12091392,-58720256,63504384,487587840,-1997733888,2501902336,2267447296,-11377049600,11054776320]),(⟨4,2,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,3,0⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨4,4,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,5,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,0,0⟩,[8192,-491520,9207808,-80740352,361373696,-643825664,-1312555008,10124918784,-25044164608,28999319552,-892633088,-40701132800,39251959808,-5239406592]),(⟨5,0,2⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨5,0,3⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨5,1,2⟩,[32768,-1048576,12091392,-58720256,63504384,487587840,-1997733888,2501902336,2267447296,-11377049600,11054776320]),(⟨5,1,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,2,0⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨5,2,1⟩,[32768,-1048576,12091392,-58720256,63504384,487587840,-1997733888,2501902336,2267447296,-11377049600,11054776320]),(⟨5,2,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,3,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨5,3,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,4,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨6,0,0⟩,[0,-81920,2473984,-27869184,150847488,-356417536,-259555328,4107763712,-11853791232,15835054080,-4308942848,-15246704640,14910013440]),(⟨6,0,2⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨6,2,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832])]


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

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[8192,-360448,7020544,-80592896,605929472,-3093446656,10474053632,-19728236544,-5879316480,168439054336,-570073292800,1063007830016,-1085825171456,174493646848,1106226159616,-1470031036416,731069194240,-79478784000]),(⟨0,1,1⟩,[0,-90112,3276800,-51740672,471752704,-2745311232,10401857536,-23552016384,14628036608,101239775232,-410994573312,786851627008,-762012590080,20291461120,853893038080,-909539950592,324873543680]),(⟨0,1,2⟩,[-8192,352256,-6184960,58572800,-323608576,967811072,-474390528,-8548089856,38096936960,-79701303296,71025385472,53784723456,-211376349184,191628337152,-8266997760,-60018524160]),(⟨0,1,3⟩,[0,114688,-3833856,52969472,-399261696,1772814336,-4341415936,2353954816,21610594304,-80463675392,134066077696,-87380377600,-65018216448,148950581248,-74689986560]),(⟨0,1,4⟩,[0,0,-327680,7929856,-78970880,425525248,-1322909696,2062680064,668860416,-10416422912,20187119616,-10341777408,-15494348800,17523867648]),(⟨0,2,0⟩,[-16384,516096,-6635520,42745856,-106176512,-432529408,4776181760,-18865487872,35689390080,1646796800,-191234228224,512415252480,-647355523072,230773219328,489894002688,-712443953152,302991073280]),(⟨0,2,1⟩,[0,114688,-2998272,31326208,-159039488,275415040,1340309504,-10320166912,32369049600,-54534946816,33197080576,55517609984,-130545991680,71067566080,58474823680,-66910699520]),(⟨0,2,2⟩,[16384,-557056,7700480,-55132160,206225408,-250232832,-1120141312,5948014592,-12762628096,12745637888,2864152576,-24110055424,23918755840,-5946228736,433520640]),(⟨0,2,3⟩,[-16384,376832,-3801088,26034176,-149667840,671809536,-1984954368,3312484352,-2392440832,249151488,-868876288,543834112,2254028800,-584220672]),(⟨0,2,4⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨0,2,5⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨0,2,6⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨0,3,0⟩,[-16384,802816,-15466496,159662080,-980926464,3571236864,-5907611648,-9860661248,85547958272,-239478390784,357182603264,-206309638144,-234166566912,530104532992,-339912622080,40737751040]),(⟨0,3,1⟩,[0,90112,-3072000,42418176,-313802752,1334353920,-2907381760,-383942656,23118249984,-73597542400,113078886400,-60448620544,-78265729024,143698386944,-68036648960]),(⟨0,3,2⟩,[-8192,212992,-2523136,20332544,-130129920,632946688,-2116681728,4495015936,-5479161856,2087665664,6458212352,-16193077248,14222303232,-1847623680]),(⟨0,3,3⟩,[0,147456,-3522560,36847616,-221888512,831553536,-1918337024,2473754624,-1495105536,1207255040,-2502606848,-657244160,4128194560]),(⟨0,3,4⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨0,3,5⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨0,4,0⟩,[16384,-417792,3022848,8667136,-261865472,1721393152,-5259911168,4084695040,27194408960,-112669466624,203743977472,-160803307520,-61409214464,227560890368,-134650306560]),(⟨0,4,1⟩,[0,0,-327680,7929856,-78970880,425525248,-1322909696,2062680064,668860416,-10416422912,20187119616,-10341777408,-15494348800,17523867648]),(⟨0,4,2⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨0,4,3⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨0,5,0⟩,[8192,-491520,9207808,-80740352,361373696,-643825664,-1312555008,10124918784,-25044164608,28999319552,-892633088,-40701132800,39251959808,-5239406592]),(⟨0,5,2⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨0,5,3⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨0,6,0⟩,[0,-81920,2473984,-27869184,150847488,-356417536,-259555328,4107763712,-11853791232,15835054080,-4308942848,-15246704640,14910013440]),(⟨0,6,2⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨1,0,0⟩,[8192,-360448,7020544,-80592896,605929472,-3093446656,10474053632,-19728236544,-5879316480,168439054336,-570073292800,1063007830016,-1085825171456,174493646848,1106226159616,-1470031036416,731069194240,-79478784000]),(⟨1,0,1⟩,[0,-90112,3276800,-51740672,471752704,-2745311232,10401857536,-23552016384,14628036608,101239775232,-410994573312,786851627008,-762012590080,20291461120,853893038080,-909539950592,324873543680]),(⟨1,0,2⟩,[-8192,352256,-6184960,58572800,-323608576,967811072,-474390528,-8548089856,38096936960,-79701303296,71025385472,53784723456,-211376349184,191628337152,-8266997760,-60018524160]),(⟨1,0,3⟩,[0,114688,-3833856,52969472,-399261696,1772814336,-4341415936,2353954816,21610594304,-80463675392,134066077696,-87380377600,-65018216448,148950581248,-74689986560]),(⟨1,0,4⟩,[0,0,-327680,7929856,-78970880,425525248,-1322909696,2062680064,668860416,-10416422912,20187119616,-10341777408,-15494348800,17523867648]),(⟨1,1,0⟩,[0,-147456,5406720,-85557248,777764864,-4486512640,16683040768,-35929587712,12355256320,200195719168,-744759590912,1393688346624,-1349475614720,68088545280,1484064030720,-1654035382272,630094151680]),(⟨1,1,1⟩,[0,0,688128,-19365888,234946560,-1632436224,7159382016,-19931627520,29998055424,6045696000,-140349702144,310718201856,-274253414400,-81949163520,371069583360,-226418196480]),(⟨1,1,2⟩,[0,32768,-1114112,15794176,-122486784,567771136,-1554513920,1916665856,2385903616,-14323056640,23132569600,-5567873024,-28977987584,29570924544,-3821404160]),(⟨1,1,3⟩,[0,0,-327680,7929856,-78970880,425525248,-1322909696,2062680064,668860416,-10416422912,20187119616,-10341777408,-15494348800,17523867648]),(⟨1,2,0⟩,[-8192,466944,-9412608,96354304,-560963584,1787371520,-1520541696,-12224380928,60466634752,-136251482112,151005700096,5729599488,-250504536064,290012291072,-73482035200,-51456491520]),(⟨1,2,1⟩,[0,32768,-1114112,15794176,-122486784,567771136,-1554513920,1916665856,2385903616,-14323056640,23132569600,-5567873024,-28977987584,29570924544,-3821404160]),(⟨1,2,3⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨1,3,0⟩,[0,172032,-5791744,79593472,-590577664,2539397120,-5694283776,53346304,42342940672,-139738161152,224012394496,-142261125120,-114305957888,263078043648,-138905231360]),(⟨1,3,1⟩,[0,0,-327680,7929856,-78970880,425525248,-1322909696,2062680064,668860416,-10416422912,20187119616,-10341777408,-15494348800,17523867648]),(⟨1,3,2⟩,[-32768,1261568,-18989056,145637376,-595673088,1023311872,1533050880,-11670224896,22959030272,-6832635904,-52009287680,96152010752,-57935216640]),(⟨1,3,3⟩,[0,131072,-3407872,33947648,-160432128,330563584,115867648,-2266234880,5011144704,-1259732992,-11573395456,12992774144]),(⟨1,4,0⟩,[0,0,-327680,7929856,-78970880,425525248,-1322909696,2062680064,668860416,-10416422912,20187119616,-10341777408,-15494348800,17523867648]),(⟨1,4,2⟩,[65536,-1703936,16187392,-62062592,11665408,623902720,-1847197696,1715863552,2440888320,-9668788224,10124197888,-1473970176]),(⟨1,4,5⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,5,2⟩,[32768,-1048576,12091392,-58720256,63504384,487587840,-1997733888,2501902336,2267447296,-11377049600,11054776320]),(⟨1,5,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,0,0⟩,[-16384,516096,-6635520,42745856,-106176512,-432529408,4776181760,-18865487872,35689390080,1646796800,-191234228224,512415252480,-647355523072,230773219328,489894002688,-712443953152,302991073280]),(⟨2,0,1⟩,[0,114688,-2998272,31326208,-159039488,275415040,1340309504,-10320166912,32369049600,-54534946816,33197080576,55517609984,-130545991680,71067566080,58474823680,-66910699520]),(⟨2,0,2⟩,[16384,-557056,7700480,-55132160,206225408,-250232832,-1120141312,5948014592,-12762628096,12745637888,2864152576,-24110055424,23918755840,-5946228736,433520640]),(⟨2,0,3⟩,[-16384,376832,-3801088,26034176,-149667840,671809536,-1984954368,3312484352,-2392440832,249151488,-868876288,543834112,2254028800,-584220672]),(⟨2,0,4⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨2,0,5⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨2,0,6⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨2,1,0⟩,[-8192,466944,-9412608,96354304,-560963584,1787371520,-1520541696,-12224380928,60466634752,-136251482112,151005700096,5729599488,-250504536064,290012291072,-73482035200,-51456491520]),(⟨2,1,1⟩,[0,32768,-1114112,15794176,-122486784,567771136,-1554513920,1916665856,2385903616,-14323056640,23132569600,-5567873024,-28977987584,29570924544,-3821404160]),(⟨2,1,3⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨2,2,0⟩,[32768,-1114112,15400960,-110264320,412450816,-500465664,-2240282624,11896029184,-25525256192,25491275776,5728305152,-48220110848,47837511680,-11892457472,867041280]),(⟨2,2,2⟩,[-65536,2293760,-31981568,226557952,-818610176,858652672,4724883456,-21706440704,35559374848,962527232,-105824911360,177714561024,-105088614400]),(⟨2,2,3⟩,[32768,-786432,6651904,-20316160,-23789568,318242816,-616890368,-1443627008,7817297920,-5418778624,-19078348800,25439633408]),(⟨2,3,0⟩,[-8192,49152,1441792,-17186816,40787968,330465280,-2707095552,8966209536,-16457883648,15668068352,2348351488,-28175187968,27864145920,-3835625472]),(⟨2,3,1⟩,[-32768,1261568,-18989056,145637376,-595673088,1023311872,1533050880,-11670224896,22959030272,-6832635904,-52009287680,96152010752,-57935216640]),(⟨2,3,2⟩,[98304,-2490368,22839296,-82378752,-12124160,942145536,-2464088064,272236544,10258186240,-15087566848,-8954150912,23965663232]),(⟨2,3,3⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨2,3,5⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,4,0⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨2,4,1⟩,[65536,-1703936,16187392,-62062592,11665408,623902720,-1847197696,1715863552,2440888320,-9668788224,10124197888,-1473970176]),(⟨2,4,2⟩,[32768,-1048576,12091392,-58720256,63504384,487587840,-1997733888,2501902336,2267447296,-11377049600,11054776320]),(⟨2,4,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,5,0⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨2,5,1⟩,[32768,-1048576,12091392,-58720256,63504384,487587840,-1997733888,2501902336,2267447296,-11377049600,11054776320]),(⟨2,5,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,6,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨3,0,0⟩,[-16384,802816,-15466496,159662080,-980926464,3571236864,-5907611648,-9860661248,85547958272,-239478390784,357182603264,-206309638144,-234166566912,530104532992,-339912622080,40737751040]),(⟨3,0,1⟩,[0,90112,-3072000,42418176,-313802752,1334353920,-2907381760,-383942656,23118249984,-73597542400,113078886400,-60448620544,-78265729024,143698386944,-68036648960]),(⟨3,0,2⟩,[-8192,212992,-2523136,20332544,-130129920,632946688,-2116681728,4495015936,-5479161856,2087665664,6458212352,-16193077248,14222303232,-1847623680]),(⟨3,0,3⟩,[0,147456,-3522560,36847616,-221888512,831553536,-1918337024,2473754624,-1495105536,1207255040,-2502606848,-657244160,4128194560]),(⟨3,0,4⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨3,0,5⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨3,1,0⟩,[0,172032,-5791744,79593472,-590577664,2539397120,-5694283776,53346304,42342940672,-139738161152,224012394496,-142261125120,-114305957888,263078043648,-138905231360]),(⟨3,1,1⟩,[0,0,-327680,7929856,-78970880,425525248,-1322909696,2062680064,668860416,-10416422912,20187119616,-10341777408,-15494348800,17523867648]),(⟨3,1,2⟩,[-32768,1261568,-18989056,145637376,-595673088,1023311872,1533050880,-11670224896,22959030272,-6832635904,-52009287680,96152010752,-57935216640]),(⟨3,1,3⟩,[0,131072,-3407872,33947648,-160432128,330563584,115867648,-2266234880,5011144704,-1259732992,-11573395456,12992774144]),(⟨3,2,0⟩,[-8192,49152,1441792,-17186816,40787968,330465280,-2707095552,8966209536,-16457883648,15668068352,2348351488,-28175187968,27864145920,-3835625472]),(⟨3,2,1⟩,[-32768,1261568,-18989056,145637376,-595673088,1023311872,1533050880,-11670224896,22959030272,-6832635904,-52009287680,96152010752,-57935216640]),(⟨3,2,2⟩,[98304,-2490368,22839296,-82378752,-12124160,942145536,-2464088064,272236544,10258186240,-15087566848,-8954150912,23965663232]),(⟨3,2,3⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨3,2,5⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,3,0⟩,[0,65536,-1048576,8978432,-71041024,475136000,-2177892352,6581518336,-13348896768,17042309120,-6811549696,-15903948800,19038208000]),(⟨3,3,1⟩,[0,131072,-3407872,33947648,-160432128,330563584,115867648,-2266234880,5011144704,-1259732992,-11573395456,12992774144]),(⟨3,3,2⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨3,4,0⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨3,5,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨3,5,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,0,0⟩,[16384,-417792,3022848,8667136,-261865472,1721393152,-5259911168,4084695040,27194408960,-112669466624,203743977472,-160803307520,-61409214464,227560890368,-134650306560]),(⟨4,0,1⟩,[0,0,-327680,7929856,-78970880,425525248,-1322909696,2062680064,668860416,-10416422912,20187119616,-10341777408,-15494348800,17523867648]),(⟨4,0,2⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨4,0,3⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨4,1,0⟩,[0,0,-327680,7929856,-78970880,425525248,-1322909696,2062680064,668860416,-10416422912,20187119616,-10341777408,-15494348800,17523867648]),(⟨4,1,2⟩,[65536,-1703936,16187392,-62062592,11665408,623902720,-1847197696,1715863552,2440888320,-9668788224,10124197888,-1473970176]),(⟨4,1,5⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,2,0⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨4,2,1⟩,[65536,-1703936,16187392,-62062592,11665408,623902720,-1847197696,1715863552,2440888320,-9668788224,10124197888,-1473970176]),(⟨4,2,2⟩,[32768,-1048576,12091392,-58720256,63504384,487587840,-1997733888,2501902336,2267447296,-11377049600,11054776320]),(⟨4,2,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,3,0⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨4,4,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,5,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,0,0⟩,[8192,-491520,9207808,-80740352,361373696,-643825664,-1312555008,10124918784,-25044164608,28999319552,-892633088,-40701132800,39251959808,-5239406592]),(⟨5,0,2⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨5,0,3⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨5,1,2⟩,[32768,-1048576,12091392,-58720256,63504384,487587840,-1997733888,2501902336,2267447296,-11377049600,11054776320]),(⟨5,1,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,2,0⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨5,2,1⟩,[32768,-1048576,12091392,-58720256,63504384,487587840,-1997733888,2501902336,2267447296,-11377049600,11054776320]),(⟨5,2,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,3,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨5,3,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,4,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨6,0,0⟩,[0,-81920,2473984,-27869184,150847488,-356417536,-259555328,4107763712,-11853791232,15835054080,-4308942848,-15246704640,14910013440]),(⟨6,0,2⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨6,2,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[16384,-647168,11583488,-124059648,878108672,-4229226496,13323026432,-21057650688,-28785647616,283382685696,-889435308032,1647955771392,-1766090104832,510158233600,1474021015552,-2344903655424,1483877605376,-371384565760,29314252800]),(⟨0,0,1⟩,[8192,-475136,10764288,-134561792,1058267136,-5501550592,18549620736,-33323270144,-20803739648,333874298880,-1088827506688,2003644923904,-2049268211712,389936775168,1955714318336,-2677854519296,1396385464320,-192053657600]),(⟨0,0,2⟩,[-32768,1146880,-17080320,140345344,-666705920,1514258432,1684611072,-24224350208,80496730112,-122197049344,-10007175168,419014311936,-801233887232,565255323648,239086657536,-643990700032,297291079680]),(⟨0,0,3⟩,[-16384,966656,-20168704,217399296,-1375551488,5158092800,-9140092928,-11415928832,117178580992,-340718960640,528345513984,-346572668928,-260240162816,701407019008,-474664812544,66876293120]),(⟨0,0,4⟩,[16384,-417792,3022848,8667136,-261865472,1721393152,-5259911168,4084695040,27194408960,-112669466624,203743977472,-160803307520,-61409214464,227560890368,-134650306560]),(⟨0,0,5⟩,[8192,-491520,9207808,-80740352,361373696,-643825664,-1312555008,10124918784,-25044164608,28999319552,-892633088,-40701132800,39251959808,-5239406592]),(⟨0,0,6⟩,[0,-81920,2473984,-27869184,150847488,-356417536,-259555328,4107763712,-11853791232,15835054080,-4308942848,-15246704640,14910013440]),(⟨0,1,0⟩,[8192,-475136,10764288,-134561792,1058267136,-5501550592,18549620736,-33323270144,-20803739648,333874298880,-1088827506688,2003644923904,-2049268211712,389936775168,1955714318336,-2677854519296,1396385464320,-192053657600]),(⟨0,1,1⟩,[0,-147456,5406720,-85557248,777764864,-4486512640,16683040768,-35929587712,12355256320,200195719168,-744759590912,1393688346624,-1349475614720,68088545280,1484064030720,-1654035382272,630094151680]),(⟨0,1,2⟩,[-8192,466944,-9412608,96354304,-560963584,1787371520,-1520541696,-12224380928,60466634752,-136251482112,151005700096,5729599488,-250504536064,290012291072,-73482035200,-51456491520]),(⟨0,1,3⟩,[0,172032,-5791744,79593472,-590577664,2539397120,-5694283776,53346304,42342940672,-139738161152,224012394496,-142261125120,-114305957888,263078043648,-138905231360]),(⟨0,1,4⟩,[0,0,-327680,7929856,-78970880,425525248,-1322909696,2062680064,668860416,-10416422912,20187119616,-10341777408,-15494348800,17523867648]),(⟨0,2,0⟩,[-32768,1146880,-17080320,140345344,-666705920,1514258432,1684611072,-24224350208,80496730112,-122197049344,-10007175168,419014311936,-801233887232,565255323648,239086657536,-643990700032,297291079680]),(⟨0,2,1⟩,[-8192,466944,-9412608,96354304,-560963584,1787371520,-1520541696,-12224380928,60466634752,-136251482112,151005700096,5729599488,-250504536064,290012291072,-73482035200,-51456491520]),(⟨0,2,2⟩,[32768,-1114112,15400960,-110264320,412450816,-500465664,-2240282624,11896029184,-25525256192,25491275776,5728305152,-48220110848,47837511680,-11892457472,867041280]),(⟨0,2,3⟩,[-8192,49152,1441792,-17186816,40787968,330465280,-2707095552,8966209536,-16457883648,15668068352,2348351488,-28175187968,27864145920,-3835625472]),(⟨0,2,4⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨0,2,5⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨0,2,6⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨0,3,0⟩,[-16384,966656,-20168704,217399296,-1375551488,5158092800,-9140092928,-11415928832,117178580992,-340718960640,528345513984,-346572668928,-260240162816,701407019008,-474664812544,66876293120]),(⟨0,3,1⟩,[0,172032,-5791744,79593472,-590577664,2539397120,-5694283776,53346304,42342940672,-139738161152,224012394496,-142261125120,-114305957888,263078043648,-138905231360]),(⟨0,3,2⟩,[-8192,49152,1441792,-17186816,40787968,330465280,-2707095552,8966209536,-16457883648,15668068352,2348351488,-28175187968,27864145920,-3835625472]),(⟨0,3,3⟩,[0,65536,-1048576,8978432,-71041024,475136000,-2177892352,6581518336,-13348896768,17042309120,-6811549696,-15903948800,19038208000]),(⟨0,3,4⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨0,3,5⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨0,4,0⟩,[16384,-417792,3022848,8667136,-261865472,1721393152,-5259911168,4084695040,27194408960,-112669466624,203743977472,-160803307520,-61409214464,227560890368,-134650306560]),(⟨0,4,1⟩,[0,0,-327680,7929856,-78970880,425525248,-1322909696,2062680064,668860416,-10416422912,20187119616,-10341777408,-15494348800,17523867648]),(⟨0,4,2⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨0,4,3⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨0,5,0⟩,[8192,-491520,9207808,-80740352,361373696,-643825664,-1312555008,10124918784,-25044164608,28999319552,-892633088,-40701132800,39251959808,-5239406592]),(⟨0,5,2⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨0,5,3⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨0,6,0⟩,[0,-81920,2473984,-27869184,150847488,-356417536,-259555328,4107763712,-11853791232,15835054080,-4308942848,-15246704640,14910013440]),(⟨0,6,2⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨1,0,0⟩,[8192,-475136,10764288,-134561792,1058267136,-5501550592,18549620736,-33323270144,-20803739648,333874298880,-1088827506688,2003644923904,-2049268211712,389936775168,1955714318336,-2677854519296,1396385464320,-192053657600]),(⟨1,0,1⟩,[0,-147456,5406720,-85557248,777764864,-4486512640,16683040768,-35929587712,12355256320,200195719168,-744759590912,1393688346624,-1349475614720,68088545280,1484064030720,-1654035382272,630094151680]),(⟨1,0,2⟩,[-8192,466944,-9412608,96354304,-560963584,1787371520,-1520541696,-12224380928,60466634752,-136251482112,151005700096,5729599488,-250504536064,290012291072,-73482035200,-51456491520]),(⟨1,0,3⟩,[0,172032,-5791744,79593472,-590577664,2539397120,-5694283776,53346304,42342940672,-139738161152,224012394496,-142261125120,-114305957888,263078043648,-138905231360]),(⟨1,0,4⟩,[0,0,-327680,7929856,-78970880,425525248,-1322909696,2062680064,668860416,-10416422912,20187119616,-10341777408,-15494348800,17523867648]),(⟨1,1,0⟩,[0,-147456,5406720,-85557248,777764864,-4486512640,16683040768,-35929587712,12355256320,200195719168,-744759590912,1393688346624,-1349475614720,68088545280,1484064030720,-1654035382272,630094151680]),(⟨1,1,1⟩,[0,0,688128,-19365888,234946560,-1632436224,7159382016,-19931627520,29998055424,6045696000,-140349702144,310718201856,-274253414400,-81949163520,371069583360,-226418196480]),(⟨1,1,2⟩,[0,32768,-1114112,15794176,-122486784,567771136,-1554513920,1916665856,2385903616,-14323056640,23132569600,-5567873024,-28977987584,29570924544,-3821404160]),(⟨1,1,3⟩,[0,0,-327680,7929856,-78970880,425525248,-1322909696,2062680064,668860416,-10416422912,20187119616,-10341777408,-15494348800,17523867648]),(⟨1,2,0⟩,[-8192,466944,-9412608,96354304,-560963584,1787371520,-1520541696,-12224380928,60466634752,-136251482112,151005700096,5729599488,-250504536064,290012291072,-73482035200,-51456491520]),(⟨1,2,1⟩,[0,32768,-1114112,15794176,-122486784,567771136,-1554513920,1916665856,2385903616,-14323056640,23132569600,-5567873024,-28977987584,29570924544,-3821404160]),(⟨1,2,2⟩,[-65536,1998848,-24805376,158564352,-512262144,327942144,3844014080,-15731589120,25306202112,-26050560,-75435376640,137111371776,-100037066752,19379978240]),(⟨1,2,3⟩,[-32768,1261568,-18989056,145637376,-595673088,1023311872,1533050880,-11670224896,22959030272,-6832635904,-52009287680,96152010752,-57935216640]),(⟨1,2,4⟩,[65536,-1703936,16187392,-62062592,11665408,623902720,-1847197696,1715863552,2440888320,-9668788224,10124197888,-1473970176]),(⟨1,2,5⟩,[32768,-1048576,12091392,-58720256,63504384,487587840,-1997733888,2501902336,2267447296,-11377049600,11054776320]),(⟨1,3,0⟩,[0,172032,-5791744,79593472,-590577664,2539397120,-5694283776,53346304,42342940672,-139738161152,224012394496,-142261125120,-114305957888,263078043648,-138905231360]),(⟨1,3,1⟩,[0,0,-327680,7929856,-78970880,425525248,-1322909696,2062680064,668860416,-10416422912,20187119616,-10341777408,-15494348800,17523867648]),(⟨1,3,2⟩,[-32768,1261568,-18989056,145637376,-595673088,1023311872,1533050880,-11670224896,22959030272,-6832635904,-52009287680,96152010752,-57935216640]),(⟨1,3,3⟩,[0,131072,-3407872,33947648,-160432128,330563584,115867648,-2266234880,5011144704,-1259732992,-11573395456,12992774144]),(⟨1,4,0⟩,[0,0,-327680,7929856,-78970880,425525248,-1322909696,2062680064,668860416,-10416422912,20187119616,-10341777408,-15494348800,17523867648]),(⟨1,4,2⟩,[65536,-1703936,16187392,-62062592,11665408,623902720,-1847197696,1715863552,2440888320,-9668788224,10124197888,-1473970176]),(⟨1,4,5⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,5,2⟩,[32768,-1048576,12091392,-58720256,63504384,487587840,-1997733888,2501902336,2267447296,-11377049600,11054776320]),(⟨1,5,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,0,0⟩,[-32768,1146880,-17080320,140345344,-666705920,1514258432,1684611072,-24224350208,80496730112,-122197049344,-10007175168,419014311936,-801233887232,565255323648,239086657536,-643990700032,297291079680]),(⟨2,0,1⟩,[-8192,466944,-9412608,96354304,-560963584,1787371520,-1520541696,-12224380928,60466634752,-136251482112,151005700096,5729599488,-250504536064,290012291072,-73482035200,-51456491520]),(⟨2,0,2⟩,[32768,-1114112,15400960,-110264320,412450816,-500465664,-2240282624,11896029184,-25525256192,25491275776,5728305152,-48220110848,47837511680,-11892457472,867041280]),(⟨2,0,3⟩,[-8192,49152,1441792,-17186816,40787968,330465280,-2707095552,8966209536,-16457883648,15668068352,2348351488,-28175187968,27864145920,-3835625472]),(⟨2,0,4⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨2,0,5⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨2,0,6⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨2,1,0⟩,[-8192,466944,-9412608,96354304,-560963584,1787371520,-1520541696,-12224380928,60466634752,-136251482112,151005700096,5729599488,-250504536064,290012291072,-73482035200,-51456491520]),(⟨2,1,1⟩,[0,32768,-1114112,15794176,-122486784,567771136,-1554513920,1916665856,2385903616,-14323056640,23132569600,-5567873024,-28977987584,29570924544,-3821404160]),(⟨2,1,2⟩,[-65536,1998848,-24805376,158564352,-512262144,327942144,3844014080,-15731589120,25306202112,-26050560,-75435376640,137111371776,-100037066752,19379978240]),(⟨2,1,3⟩,[-32768,1261568,-18989056,145637376,-595673088,1023311872,1533050880,-11670224896,22959030272,-6832635904,-52009287680,96152010752,-57935216640]),(⟨2,1,4⟩,[65536,-1703936,16187392,-62062592,11665408,623902720,-1847197696,1715863552,2440888320,-9668788224,10124197888,-1473970176]),(⟨2,1,5⟩,[32768,-1048576,12091392,-58720256,63504384,487587840,-1997733888,2501902336,2267447296,-11377049600,11054776320]),(⟨2,2,0⟩,[32768,-1114112,15400960,-110264320,412450816,-500465664,-2240282624,11896029184,-25525256192,25491275776,5728305152,-48220110848,47837511680,-11892457472,867041280]),(⟨2,2,1⟩,[-65536,1998848,-24805376,158564352,-512262144,327942144,3844014080,-15731589120,25306202112,-26050560,-75435376640,137111371776,-100037066752,19379978240]),(⟨2,2,2⟩,[-98304,3440640,-47972352,339836928,-1227915264,1287979008,7087325184,-32559661056,53339062272,1443790848,-158737367040,266571841536,-157632921600]),(⟨2,2,3⟩,[98304,-2490368,22839296,-82378752,-12124160,942145536,-2464088064,272236544,10258186240,-15087566848,-8954150912,23965663232]),(⟨2,2,4⟩,[32768,-1048576,12091392,-58720256,63504384,487587840,-1997733888,2501902336,2267447296,-11377049600,11054776320]),(⟨2,3,0⟩,[-8192,49152,1441792,-17186816,40787968,330465280,-2707095552,8966209536,-16457883648,15668068352,2348351488,-28175187968,27864145920,-3835625472]),(⟨2,3,1⟩,[-32768,1261568,-18989056,145637376,-595673088,1023311872,1533050880,-11670224896,22959030272,-6832635904,-52009287680,96152010752,-57935216640]),(⟨2,3,2⟩,[98304,-2490368,22839296,-82378752,-12124160,942145536,-2464088064,272236544,10258186240,-15087566848,-8954150912,23965663232]),(⟨2,3,3⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨2,3,5⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,4,0⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨2,4,1⟩,[65536,-1703936,16187392,-62062592,11665408,623902720,-1847197696,1715863552,2440888320,-9668788224,10124197888,-1473970176]),(⟨2,4,2⟩,[32768,-1048576,12091392,-58720256,63504384,487587840,-1997733888,2501902336,2267447296,-11377049600,11054776320]),(⟨2,4,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,5,0⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨2,5,1⟩,[32768,-1048576,12091392,-58720256,63504384,487587840,-1997733888,2501902336,2267447296,-11377049600,11054776320]),(⟨2,5,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,6,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨3,0,0⟩,[-16384,966656,-20168704,217399296,-1375551488,5158092800,-9140092928,-11415928832,117178580992,-340718960640,528345513984,-346572668928,-260240162816,701407019008,-474664812544,66876293120]),(⟨3,0,1⟩,[0,172032,-5791744,79593472,-590577664,2539397120,-5694283776,53346304,42342940672,-139738161152,224012394496,-142261125120,-114305957888,263078043648,-138905231360]),(⟨3,0,2⟩,[-8192,49152,1441792,-17186816,40787968,330465280,-2707095552,8966209536,-16457883648,15668068352,2348351488,-28175187968,27864145920,-3835625472]),(⟨3,0,3⟩,[0,65536,-1048576,8978432,-71041024,475136000,-2177892352,6581518336,-13348896768,17042309120,-6811549696,-15903948800,19038208000]),(⟨3,0,4⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨3,0,5⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨3,1,0⟩,[0,172032,-5791744,79593472,-590577664,2539397120,-5694283776,53346304,42342940672,-139738161152,224012394496,-142261125120,-114305957888,263078043648,-138905231360]),(⟨3,1,1⟩,[0,0,-327680,7929856,-78970880,425525248,-1322909696,2062680064,668860416,-10416422912,20187119616,-10341777408,-15494348800,17523867648]),(⟨3,1,2⟩,[-32768,1261568,-18989056,145637376,-595673088,1023311872,1533050880,-11670224896,22959030272,-6832635904,-52009287680,96152010752,-57935216640]),(⟨3,1,3⟩,[0,131072,-3407872,33947648,-160432128,330563584,115867648,-2266234880,5011144704,-1259732992,-11573395456,12992774144]),(⟨3,2,0⟩,[-8192,49152,1441792,-17186816,40787968,330465280,-2707095552,8966209536,-16457883648,15668068352,2348351488,-28175187968,27864145920,-3835625472]),(⟨3,2,1⟩,[-32768,1261568,-18989056,145637376,-595673088,1023311872,1533050880,-11670224896,22959030272,-6832635904,-52009287680,96152010752,-57935216640]),(⟨3,2,2⟩,[98304,-2490368,22839296,-82378752,-12124160,942145536,-2464088064,272236544,10258186240,-15087566848,-8954150912,23965663232]),(⟨3,2,3⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨3,2,5⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,3,0⟩,[0,65536,-1048576,8978432,-71041024,475136000,-2177892352,6581518336,-13348896768,17042309120,-6811549696,-15903948800,19038208000]),(⟨3,3,1⟩,[0,131072,-3407872,33947648,-160432128,330563584,115867648,-2266234880,5011144704,-1259732992,-11573395456,12992774144]),(⟨3,3,2⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨3,4,0⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨3,5,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨3,5,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,0,0⟩,[16384,-417792,3022848,8667136,-261865472,1721393152,-5259911168,4084695040,27194408960,-112669466624,203743977472,-160803307520,-61409214464,227560890368,-134650306560]),(⟨4,0,1⟩,[0,0,-327680,7929856,-78970880,425525248,-1322909696,2062680064,668860416,-10416422912,20187119616,-10341777408,-15494348800,17523867648]),(⟨4,0,2⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨4,0,3⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨4,1,0⟩,[0,0,-327680,7929856,-78970880,425525248,-1322909696,2062680064,668860416,-10416422912,20187119616,-10341777408,-15494348800,17523867648]),(⟨4,1,2⟩,[65536,-1703936,16187392,-62062592,11665408,623902720,-1847197696,1715863552,2440888320,-9668788224,10124197888,-1473970176]),(⟨4,1,5⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,2,0⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨4,2,1⟩,[65536,-1703936,16187392,-62062592,11665408,623902720,-1847197696,1715863552,2440888320,-9668788224,10124197888,-1473970176]),(⟨4,2,2⟩,[32768,-1048576,12091392,-58720256,63504384,487587840,-1997733888,2501902336,2267447296,-11377049600,11054776320]),(⟨4,2,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,3,0⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨4,4,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,5,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,0,0⟩,[8192,-491520,9207808,-80740352,361373696,-643825664,-1312555008,10124918784,-25044164608,28999319552,-892633088,-40701132800,39251959808,-5239406592]),(⟨5,0,2⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨5,0,3⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨5,1,2⟩,[32768,-1048576,12091392,-58720256,63504384,487587840,-1997733888,2501902336,2267447296,-11377049600,11054776320]),(⟨5,1,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,2,0⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨5,2,1⟩,[32768,-1048576,12091392,-58720256,63504384,487587840,-1997733888,2501902336,2267447296,-11377049600,11054776320]),(⟨5,2,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,3,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨5,3,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,4,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨6,0,0⟩,[0,-81920,2473984,-27869184,150847488,-356417536,-259555328,4107763712,-11853791232,15835054080,-4308942848,-15246704640,14910013440]),(⟨6,0,2⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨6,2,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832])]


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
    (Poly.add (Poly.scale (K.ofRat r713) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 7 12).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r712*r712 : ℚ)=r713 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 7 12 r712 r712 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 7=12 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 7 12).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C127

#print axioms Coulomb8.Columns.C127.sound
