import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C071

def r0 : ℚ := { num := 384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -9600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 105600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -676608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 2775936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -7439616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 1798656, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -731904, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 8801664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -2477952, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 36280704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -31953408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 4095360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 6756096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -1539072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 3200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -37888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 39808, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -1377536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := 273408, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 2252800, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -15819392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 16842624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -31716864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 49654656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -40045568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 9976832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 417024, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -6144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 48128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -257024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 1023872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -173056, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 5597184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -6566400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 6314624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -11710464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 20215808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -17110528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 5916800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -1664, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 116224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -673408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 2468608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -820992, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 8053504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -916736, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 358144, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -15167872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 3157248, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -11591296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -464896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -3328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 7808, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -380288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 1451776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -3258624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 4276224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -3545088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 4676864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -1550848, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 14583424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -1187200, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := -640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := 768, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := -105216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := 445184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -1052928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 1250560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -466432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 487680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := -2760832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := 3111936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := -4864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := 4608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := -61440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := 325632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := -121344, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := 1030656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := -420864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := 734208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := -2919936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 3205120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -4608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 28416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -10752, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 67840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 2560, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 25856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -250368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -4608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -2048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := 20992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -74240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := 5120, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 37888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 31232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -363008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -29440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 245248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -1167360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := 3497216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -6814208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 8810496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -9369600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 15355904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -29823744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 5381632, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -26867712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 1362688, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := -2944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := 27008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := -131584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := 52736, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := -588544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := 513024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := -377856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 69248, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 316032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -3074432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 5396992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -484352, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 3200, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := -53632, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 83456, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -3154944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 4137216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -3574016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 4866560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -10555136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 13730432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -1122176, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 90112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := -399360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := 491520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 768000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -2613248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -1280, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := 121088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := -327424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := 405248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := -133888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 235264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -78080, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 224512, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := 4096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := -49152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := 122880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 147456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := -9728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 66048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -207360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := 286208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := -48640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -35328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := -552448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 436224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := 9216, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := -384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := 7936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := -62208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -507648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 449536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := -512, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 233984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := -153728, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := 603392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := 508160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 6144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -79360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := 24064, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := -1043968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 178688, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -573952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 997888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -3185152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := 3267072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := -6144, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := 614400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := -215040, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 122880, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 3323904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -8454144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 1370112, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -53248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 24576, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := 24576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := -634880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -1536, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := 148992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := -305664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -121344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 1291776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -1426944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 72192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := 512, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := -51200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := 17920, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := -10240, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -276992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := 704512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -114176, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := -1024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := 13312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -6144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := 158720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -22528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 99840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -122880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -192000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 653312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := 12288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := -30720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -36864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := 192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := -4800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := 52800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -338304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 1387968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -3719808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 899328, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -365952, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 4400832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -1238976, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := 18140352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := -15976704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := 2047680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := 3378048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := -769536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 1600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -18944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := 19904, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := -688768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := 136704, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := 1126400, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := -7909696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := 8421312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -15858432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := 24827328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := -20022784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 4988416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := 208512, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := -3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 24064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -128512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 511936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := -86528, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 2798592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -3283200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := 3157312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -5855232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := 10107904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -8555264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 2958400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -832, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := 58112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := -336704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := 1234304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -410496, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := 4026752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := -458368, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 179072, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := -7583936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := 1578624, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := -5795648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -232448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := -1664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := 3904, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := -190144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := 725888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := -1629312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := 2138112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := -1772544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := 2338432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := -775424, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 7291712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -593600, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := -320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := 384, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := -52608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := 222592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -526464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 625280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -233216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 243840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -1380416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 1555968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -2432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := 2304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := 162816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -60672, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := 515328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := -210432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := 367104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := -1459968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := 1602560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := -2304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := 14208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -5376, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 33920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := 1280, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 12928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -125184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := -2304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := 10496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := -37120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := 18944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 15616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -181504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := -14720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := 122624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := -583680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := 1748608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := -3407104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := 4405248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := -4684800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := 7677952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := -14911872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := 2690816, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := -13433856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := 681344, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -1472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 13504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -65792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 26368, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -294272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 256512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -188928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 34624, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := 158016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := -1537216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := 2698496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := -242176, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := 1600, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := -26816, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 41728, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -1577472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := 2068608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := -1787008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := 2433280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := -5277568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := 6865216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := -561088, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := 45056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := -199680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := 245760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := 384000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := -1306624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -640, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 60544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := -163712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := 202624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := -66944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := 117632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := -39040, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := 112256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := 2048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -24576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := 61440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := 73728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := 33024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := -103680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := 143104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := -24320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := -17664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := -276224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := 218112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := 4608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := -192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := 3968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := -31104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := -253824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := 224768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := -256, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := 116992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := -76864, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := 301696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := 254080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := 3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := -39680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := 12032, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := -521984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := 89344, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := -286976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 498944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := -1592576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := 1633536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := -3072, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := 307200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := -107520, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := 61440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := 1661952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := -4227072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := 685056, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := -26624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := 12288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := -317440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := -768, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := 74496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := -152832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := -60672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := 645888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := -713472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := 36096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := -256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := 256, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := -25600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := 8960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := -5120, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := -138496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := 352256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := -57088, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := 6656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := -3072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := 79360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := -11264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := 49920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := -96000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := 326656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := -15360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := -18432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := 1, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := 1, den := 476, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14],[r15,r16,r17,r18,r19,r20,-88832,r21,r22,r23,r24,r25,r26,r27,r28],[0,r0,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40],[r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53],[0,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63,r64],[r65,r66,r67,r68,r69,r70,r71,r72,r73,r74,r75],[0,r76,r77,r78,r79,r80,r81,r82,r83,r84],[r85,r86,r87,r88,r89,r90,r91,r92,r93],[0,r94,r95,r96,r97,r98,r99,r100],[],[],[],[],[0,r101,r102,r103,r104,r105,r106,r107,r108,r109,r110,r111,r112,r113],[r114,r115,r116,r117,r118,r119,r120,r121,r122,r123,r124,r125,r126],[0,r54,r127,r128,r129,r130,r131,r132,r133,r134,r135,r136],[0,0,0,0,r29,r137,r138,r139,r140,r141,18432],[0,r101,r142,r143,r144,r145,r146,r147,r148,r149],[0,0,0,0,r150,r151,r152,r153,-4096],[],[],[],[],[],[0,0,r41,r154,r155,r156,r157,r158,r159,r160,r161,r162],[r163,r164,r165,r103,r166,r167,r168,r169,r170,r171,r172],[],[r85,r86,r87,r88,r89,r90,r91,r92,r93],[],[],[],[],[],[0,r173,r174,r175,r176,r177,r178,r179,r180,r181],[],[0,r94,r95,r96,r97,r98,r99,r100],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,0,0,0,r173,r182,r183,r184,r185,r186,r187,r188,-43008],[0,0,0,0,0,0,r150,r189,r190,r191,r192,4096],[0,0,0,0,r29,r137,r138,r139,r140,r141,18432],[],[0,0,0,0,r150,r151,r152,r153,-4096],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,r101,r193,r194,r195,r196,r197,r198,r199,3072],[r200,r201,r202,r203,r204,r205,r206,r207,3584],[0,0,r208,r209,r210,r29,r211,-1024],[r101,r212,r213,r214,r215,r216,-4608],[],[r208,r217,r218,r219,1024],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r220,r221,r222,r223,r224,r225,r226,r227,r228,r229,r230,r231,r232,r233,r234]),(⟨0,0,1⟩,[r235,r236,r237,r238,r239,r240,-44416,r241,r242,r243,r244,r245,r246,r247,r248]),(⟨0,0,2⟩,[0,r220,r249,r250,r251,r252,r253,r254,r255,r256,r257,r258,r259,r260]),(⟨0,0,3⟩,[r85,r261,r262,r263,r264,r265,r266,r267,r268,r269,r270,r271,r272]),(⟨0,0,4⟩,[0,r273,r274,r275,r276,r277,r278,r279,r280,r281,r282,r283]),(⟨0,0,5⟩,[r284,r285,r286,r287,r288,r289,r290,r291,r292,r293,r294]),(⟨0,0,6⟩,[0,r295,r218,r296,r297,r298,r299,r300,r301,r302]),(⟨0,0,7⟩,[r114,r303,r304,r305,r306,r307,r308,r309,r310]),(⟨0,0,8⟩,[0,r208,r311,r312,r90,r313,r314,r315]),(⟨0,1,0⟩,[r235,r236,r237,r238,r239,r240,-44416,r241,r242,r243,r244,r245,r246,r247,r248]),(⟨0,1,1⟩,[0,r316,r317,r318,r319,r320,r321,r322,r323,r324,r325,r326,r327,r328]),(⟨0,1,2⟩,[r329,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨0,1,3⟩,[0,r273,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351]),(⟨0,1,4⟩,[0,0,0,0,r249,r352,r353,r354,r355,r356,9216]),(⟨0,1,5⟩,[0,r316,r357,r358,r359,r360,r361,r362,r363,r364]),(⟨0,1,6⟩,[0,0,0,0,r365,r366,r367,r368,-2048]),(⟨0,2,0⟩,[0,r220,r249,r250,r251,r252,r253,r254,r255,r256,r257,r258,r259,r260]),(⟨0,2,1⟩,[r329,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨0,2,2⟩,[0,0,r85,r75,r369,r370,r371,r372,r373,r374,r375,r376]),(⟨0,2,3⟩,[r377,r378,r379,r318,r380,r381,r382,r383,r384,r385,r386]),(⟨0,2,5⟩,[r114,r303,r304,r305,r306,r307,r308,r309,r310]),(⟨0,3,0⟩,[r85,r261,r262,r263,r264,r265,r266,r267,r268,r269,r270,r271,r272]),(⟨0,3,1⟩,[0,r273,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351]),(⟨0,3,2⟩,[r377,r378,r379,r318,r380,r381,r382,r383,r384,r385,r386]),(⟨0,3,3⟩,[0,r387,r388,r389,r390,r391,r392,r393,r394,r395]),(⟨0,3,5⟩,[0,r208,r311,r312,r90,r313,r314,r315]),(⟨0,4,0⟩,[0,r273,r274,r275,r276,r277,r278,r279,r280,r281,r282,r283]),(⟨0,4,1⟩,[0,0,0,0,r249,r352,r353,r354,r355,r356,9216]),(⟨0,5,0⟩,[r284,r285,r286,r287,r288,r289,r290,r291,r292,r293,r294]),(⟨0,5,1⟩,[0,r316,r357,r358,r359,r360,r361,r362,r363,r364]),(⟨0,5,2⟩,[r114,r303,r304,r305,r306,r307,r308,r309,r310]),(⟨0,5,3⟩,[0,r208,r311,r312,r90,r313,r314,r315]),(⟨0,6,0⟩,[0,r295,r218,r296,r297,r298,r299,r300,r301,r302]),(⟨0,6,1⟩,[0,0,0,0,r365,r366,r367,r368,-2048]),(⟨0,7,0⟩,[r114,r303,r304,r305,r306,r307,r308,r309,r310]),(⟨0,8,0⟩,[0,r208,r311,r312,r90,r313,r314,r315]),(⟨1,0,0⟩,[r235,r236,r237,r238,r239,r240,-44416,r241,r242,r243,r244,r245,r246,r247,r248]),(⟨1,0,1⟩,[0,r316,r317,r318,r319,r320,r321,r322,r323,r324,r325,r326,r327,r328]),(⟨1,0,2⟩,[r329,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨1,0,3⟩,[0,r273,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351]),(⟨1,0,4⟩,[0,0,0,0,r249,r352,r353,r354,r355,r356,9216]),(⟨1,0,5⟩,[0,r316,r357,r358,r359,r360,r361,r362,r363,r364]),(⟨1,0,6⟩,[0,0,0,0,r365,r366,r367,r368,-2048]),(⟨1,1,0⟩,[0,r316,r317,r318,r319,r320,r321,r322,r323,r324,r325,r326,r327,r328]),(⟨1,1,1⟩,[0,0,0,0,r387,r396,r397,r398,r399,r400,r401,r402,-21504]),(⟨1,1,2⟩,[0,0,0,0,0,0,r365,r403,r404,r217,r405,2048]),(⟨1,1,3⟩,[0,0,0,0,r249,r352,r353,r354,r355,r356,9216]),(⟨1,1,5⟩,[0,0,0,0,r365,r366,r367,r368,-2048]),(⟨1,2,0⟩,[r329,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨1,2,1⟩,[0,0,0,0,0,0,r365,r403,r404,r217,r405,2048]),(⟨1,3,0⟩,[0,r273,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351]),(⟨1,3,1⟩,[0,0,0,0,r249,r352,r353,r354,r355,r356,9216]),(⟨1,4,0⟩,[0,0,0,0,r249,r352,r353,r354,r355,r356,9216]),(⟨1,5,0⟩,[0,r316,r357,r358,r359,r360,r361,r362,r363,r364]),(⟨1,5,1⟩,[0,0,0,0,r365,r366,r367,r368,-2048]),(⟨1,6,0⟩,[0,0,0,0,r365,r366,r367,r368,-2048]),(⟨2,0,0⟩,[0,r220,r249,r250,r251,r252,r253,r254,r255,r256,r257,r258,r259,r260]),(⟨2,0,1⟩,[r329,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨2,0,2⟩,[0,0,r85,r75,r369,r370,r371,r372,r373,r374,r375,r376]),(⟨2,0,3⟩,[r377,r378,r379,r318,r380,r381,r382,r383,r384,r385,r386]),(⟨2,0,5⟩,[r114,r303,r304,r305,r306,r307,r308,r309,r310]),(⟨2,1,0⟩,[r329,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨2,1,1⟩,[0,0,0,0,0,0,r365,r403,r404,r217,r405,2048]),(⟨2,2,0⟩,[0,0,r85,r75,r369,r370,r371,r372,r373,r374,r375,r376]),(⟨2,2,2⟩,[0,r316,r406,r407,r408,r409,r410,r411,r412,1536]),(⟨2,2,3⟩,[r413,r414,r415,r416,r417,r418,r419,r420,1792]),(⟨2,2,4⟩,[0,0,r200,r421,r422,r249,r423,-512]),(⟨2,2,5⟩,[r316,r424,r425,r77,r426,r427,-2304]),(⟨2,2,7⟩,[r200,r173,r428,r429,512]),(⟨2,3,0⟩,[r377,r378,r379,r318,r380,r381,r382,r383,r384,r385,r386]),(⟨2,3,2⟩,[r413,r414,r415,r416,r417,r418,r419,r420,1792]),(⟨2,4,2⟩,[0,0,r200,r421,r422,r249,r423,-512]),(⟨2,5,0⟩,[r114,r303,r304,r305,r306,r307,r308,r309,r310]),(⟨2,5,2⟩,[r316,r424,r425,r77,r426,r427,-2304]),(⟨2,7,2⟩,[r200,r173,r428,r429,512]),(⟨3,0,0⟩,[r85,r261,r262,r263,r264,r265,r266,r267,r268,r269,r270,r271,r272]),(⟨3,0,1⟩,[0,r273,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351]),(⟨3,0,2⟩,[r377,r378,r379,r318,r380,r381,r382,r383,r384,r385,r386]),(⟨3,0,3⟩,[0,r387,r388,r389,r390,r391,r392,r393,r394,r395]),(⟨3,0,5⟩,[0,r208,r311,r312,r90,r313,r314,r315]),(⟨3,1,0⟩,[0,r273,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351]),(⟨3,1,1⟩,[0,0,0,0,r249,r352,r353,r354,r355,r356,9216]),(⟨3,2,0⟩,[r377,r378,r379,r318,r380,r381,r382,r383,r384,r385,r386]),(⟨3,2,2⟩,[r413,r414,r415,r416,r417,r418,r419,r420,1792]),(⟨3,3,0⟩,[0,r387,r388,r389,r390,r391,r392,r393,r394,r395]),(⟨3,5,0⟩,[0,r208,r311,r312,r90,r313,r314,r315]),(⟨4,0,0⟩,[0,r273,r274,r275,r276,r277,r278,r279,r280,r281,r282,r283]),(⟨4,0,1⟩,[0,0,0,0,r249,r352,r353,r354,r355,r356,9216]),(⟨4,1,0⟩,[0,0,0,0,r249,r352,r353,r354,r355,r356,9216]),(⟨4,2,2⟩,[0,0,r200,r421,r422,r249,r423,-512]),(⟨5,0,0⟩,[r284,r285,r286,r287,r288,r289,r290,r291,r292,r293,r294]),(⟨5,0,1⟩,[0,r316,r357,r358,r359,r360,r361,r362,r363,r364]),(⟨5,0,2⟩,[r114,r303,r304,r305,r306,r307,r308,r309,r310]),(⟨5,0,3⟩,[0,r208,r311,r312,r90,r313,r314,r315]),(⟨5,1,0⟩,[0,r316,r357,r358,r359,r360,r361,r362,r363,r364]),(⟨5,1,1⟩,[0,0,0,0,r365,r366,r367,r368,-2048]),(⟨5,2,0⟩,[r114,r303,r304,r305,r306,r307,r308,r309,r310]),(⟨5,2,2⟩,[r316,r424,r425,r77,r426,r427,-2304]),(⟨5,3,0⟩,[0,r208,r311,r312,r90,r313,r314,r315]),(⟨6,0,0⟩,[0,r295,r218,r296,r297,r298,r299,r300,r301,r302]),(⟨6,0,1⟩,[0,0,0,0,r365,r366,r367,r368,-2048]),(⟨6,1,0⟩,[0,0,0,0,r365,r366,r367,r368,-2048]),(⟨7,0,0⟩,[r114,r303,r304,r305,r306,r307,r308,r309,r310]),(⟨7,2,2⟩,[r200,r173,r428,r429,512]),(⟨8,0,0⟩,[0,r208,r311,r312,r90,r313,r314,r315])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,-3,15,-21,3,6]),(⟨0,0,1⟩,[1,-5,10,-11,7]),(⟨0,0,2⟩,[0,0,2,-2]),(⟨0,0,3⟩,[-3,8,-9]),(⟨0,0,5⟩,[2]),(⟨0,1,0⟩,[1,-5,10,-11,7]),(⟨0,2,0⟩,[0,0,2,-2]),(⟨0,3,0⟩,[-3,8,-9]),(⟨0,5,0⟩,[2]),(⟨1,0,0⟩,[1,-5,10,-11,7]),(⟨2,0,0⟩,[0,0,2,-2]),(⟨3,0,0⟩,[-3,8,-9]),(⟨5,0,0⟩,[2])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[-256,5120,-43008,199936,-545280,801024,-457728,253696,-1684736,2508544,-513024]),(⟨0,0,1⟩,[0,1536,-21760,121088,-327424,405248,-133888,235264,-1327360,1571584]),(⟨0,0,2⟩,[256,-4608,28416,-75264,67840,43520,25856,-250368,-32256]),(⟨0,0,3⟩,[0,-2048,20992,-74240,87040,37888,31232,-363008]),(⟨0,1,0⟩,[0,1536,-21760,121088,-327424,405248,-133888,235264,-1327360,1571584]),(⟨0,1,1⟩,[0,0,0,0,4096,-49152,122880,147456,-487424]),(⟨0,2,0⟩,[256,-4608,28416,-75264,67840,43520,25856,-250368,-32256]),(⟨0,3,0⟩,[0,-2048,20992,-74240,87040,37888,31232,-363008]),(⟨1,0,0⟩,[0,1536,-21760,121088,-327424,405248,-133888,235264,-1327360,1571584]),(⟨1,0,1⟩,[0,0,0,0,4096,-49152,122880,147456,-487424]),(⟨1,1,0⟩,[0,0,0,0,4096,-49152,122880,147456,-487424]),(⟨2,0,0⟩,[256,-4608,28416,-75264,67840,43520,25856,-250368,-32256]),(⟨2,2,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨3,0,0⟩,[0,-2048,20992,-74240,87040,37888,31232,-363008])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 1 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r430) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 13 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r431) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨5,0,0⟩,[2])]

noncomputable def partial12 : Poly := [(⟨5,0,0⟩,[-512,10240,-86016,399872,-1090560,1602048,-915456,507392,-3369472,5017088,-1026048]),(⟨5,0,1⟩,[0,3072,-43520,242176,-654848,810496,-267776,470528,-2654720,3143168]),(⟨5,0,2⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨5,0,3⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨5,1,0⟩,[0,3072,-43520,242176,-654848,810496,-267776,470528,-2654720,3143168]),(⟨5,1,1⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨5,2,0⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨5,3,0⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨6,0,0⟩,[0,3072,-43520,242176,-654848,810496,-267776,470528,-2654720,3143168]),(⟨6,0,1⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨6,1,0⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨7,0,0⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨7,2,2⟩,[-2048,24576,-61440,-73728,243712]),(⟨8,0,0⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial13)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 13))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound13 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨0,5,0⟩,[2]),(⟨1,0,0⟩,[1,-5,10,-11,7]),(⟨2,0,0⟩,[0,0,2,-2]),(⟨3,0,0⟩,[-3,8,-9])]

noncomputable def partial8 : Poly := [(⟨0,5,0⟩,[-512,10240,-86016,399872,-1090560,1602048,-915456,507392,-3369472,5017088,-1026048]),(⟨0,5,1⟩,[0,3072,-43520,242176,-654848,810496,-267776,470528,-2654720,3143168]),(⟨0,5,2⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨0,5,3⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨0,6,0⟩,[0,3072,-43520,242176,-654848,810496,-267776,470528,-2654720,3143168]),(⟨0,6,1⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨0,7,0⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨0,8,0⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨1,0,0⟩,[-256,6400,-71168,468992,-2033152,6035712,-12416000,17950208,-20158720,24111360,-35897856,47958528,-44517376,23203072,-3591168]),(⟨1,0,1⟩,[0,1536,-29440,245248,-1167360,3503360,-6918656,9406464,-10592256,14870528,-24656640,31963648,-26578944,11001088]),(⟨1,0,2⟩,[256,-5888,54016,-266240,780800,-1393152,1513472,-1217536,1474304,-2322176,2612480,-1397760,-225792]),(⟨1,0,3⟩,[0,-2048,31232,-199680,690688,-1384960,1675776,-1617408,2319872,-3708416,4211712,-2541056]),(⟨1,1,0⟩,[0,1536,-29440,245248,-1167360,3503360,-6918656,9406464,-10592256,14870528,-24656640,31963648,-26578944,11001088]),(⟨1,1,1⟩,[0,0,0,0,4096,-69632,409600,-1003520,573440,2215936,-5636096,6393856,-3411968]),(⟨1,2,0⟩,[256,-5888,54016,-266240,780800,-1393152,1513472,-1217536,1474304,-2322176,2612480,-1397760,-225792]),(⟨1,3,0⟩,[0,-2048,31232,-199680,690688,-1384960,1675776,-1617408,2319872,-3708416,4211712,-2541056]),(⟨1,5,0⟩,[0,3072,-43520,242176,-654848,810496,-267776,470528,-2654720,3143168]),(⟨1,5,1⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨1,6,0⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨2,0,0⟩,[0,1536,-29952,256000,-1263616,3989248,-8409088,12099072,-13109760,16293376,-28533504,40350208,-32622080,12027136]),(⟨2,0,1⟩,[0,0,0,3072,-42496,216064,-487424,461824,-504832,2954240,-8761344,12191744,-6555136]),(⟨2,0,2⟩,[0,0,512,-9728,66048,-207360,286208,-48640,-35328,-552448,436224,64512]),(⟨2,0,3⟩,[0,0,0,-4096,46080,-190464,322560,-98304,-13312,-788480,726016]),(⟨2,1,0⟩,[0,0,0,3072,-42496,216064,-487424,461824,-504832,2954240,-8761344,12191744,-6555136]),(⟨2,1,1⟩,[0,0,0,0,0,0,8192,-106496,344064,49152,-1269760,974848]),(⟨2,2,0⟩,[0,0,512,-9728,66048,-207360,286208,-48640,-35328,-552448,436224,64512]),(⟨2,3,0⟩,[0,0,0,-4096,46080,-190464,322560,-98304,-13312,-788480,726016]),(⟨2,5,0⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨2,7,2⟩,[-2048,24576,-61440,-73728,243712]),(⟨3,0,0⟩,[1024,-23296,226304,-1253120,4356608,-9672192,13305344,-11384320,11599360,-24870656,36257280,-22280960,1248256]),(⟨3,0,1⟩,[0,-4608,77568,-551168,2146816,-4924928,6598656,-5530624,7413248,-17401856,23249152,-13169408]),(⟨3,0,2⟩,[-768,15872,-124416,494592,-1061376,1089536,-339968,566272,-2138880,1995264,290304]),(⟨3,0,3⟩,[0,6144,-79360,409088,-1043968,1250816,-573952,997888,-3185152,3267072]),(⟨3,1,0⟩,[0,-4608,77568,-551168,2146816,-4924928,6598656,-5530624,7413248,-17401856,23249152,-13169408]),(⟨3,1,1⟩,[0,0,0,0,-12288,180224,-798720,983040,1536000,-5226496,4386816]),(⟨3,2,0⟩,[-768,15872,-124416,494592,-1061376,1089536,-339968,566272,-2138880,1995264,290304]),(⟨3,2,2⟩,[-1024,17408,-102400,250880,-143360,-553984,1409024,-1598464,852992]),(⟨3,3,0⟩,[0,6144,-79360,409088,-1043968,1250816,-573952,997888,-3185152,3267072]),(⟨3,5,0⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨4,0,0⟩,[0,-6656,109312,-760576,2903552,-6517248,8552448,-7090176,9353728,-21711872,29166848,-16620800]),(⟨4,0,1⟩,[0,0,0,0,-12288,180224,-798720,983040,1536000,-5226496,4386816]),(⟨4,1,0⟩,[0,0,0,0,-12288,180224,-798720,983040,1536000,-5226496,4386816]),(⟨4,2,2⟩,[0,0,-2048,26624,-86016,-12288,317440,-243712]),(⟨5,0,0⟩,[-1280,26112,-210432,890368,-2105856,2501120,-932864,975360,-5521664,6223872,-9728]),(⟨5,0,1⟩,[0,3072,-43520,242176,-654848,810496,-267776,470528,-2654720,3143168]),(⟨5,0,2⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨5,0,3⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨5,1,0⟩,[0,3072,-43520,242176,-654848,810496,-267776,470528,-2654720,3143168]),(⟨5,1,1⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨5,2,0⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨5,2,2⟩,[3072,-45056,199680,-245760,-384000,1306624,-1096704]),(⟨5,3,0⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨6,0,0⟩,[0,9216,-122880,651264,-1698816,2061312,-841728,1468416,-5839872,6410240]),(⟨6,0,1⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨6,1,0⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨7,0,0⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨7,2,2⟩,[-2048,24576,-61440,-73728,243712]),(⟨8,0,0⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,0,5⟩,[2]),(⟨0,1,0⟩,[1,-5,10,-11,7]),(⟨0,2,0⟩,[0,0,2,-2]),(⟨0,3,0⟩,[-3,8,-9])]

noncomputable def partial4 : Poly := [(⟨0,0,5⟩,[-512,10240,-86016,399872,-1090560,1602048,-915456,507392,-3369472,5017088,-1026048]),(⟨0,0,6⟩,[0,3072,-43520,242176,-654848,810496,-267776,470528,-2654720,3143168]),(⟨0,0,7⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨0,0,8⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨0,1,0⟩,[-256,6400,-71168,468992,-2033152,6035712,-12416000,17950208,-20158720,24111360,-35897856,47958528,-44517376,23203072,-3591168]),(⟨0,1,1⟩,[0,1536,-29440,245248,-1167360,3503360,-6918656,9406464,-10592256,14870528,-24656640,31963648,-26578944,11001088]),(⟨0,1,2⟩,[256,-5888,54016,-266240,780800,-1393152,1513472,-1217536,1474304,-2322176,2612480,-1397760,-225792]),(⟨0,1,3⟩,[0,-2048,31232,-199680,690688,-1384960,1675776,-1617408,2319872,-3708416,4211712,-2541056]),(⟨0,1,5⟩,[0,3072,-43520,242176,-654848,810496,-267776,470528,-2654720,3143168]),(⟨0,1,6⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨0,2,0⟩,[0,1536,-29952,256000,-1263616,3989248,-8409088,12099072,-13109760,16293376,-28533504,40350208,-32622080,12027136]),(⟨0,2,1⟩,[0,0,0,3072,-42496,216064,-487424,461824,-504832,2954240,-8761344,12191744,-6555136]),(⟨0,2,2⟩,[0,0,512,-9728,66048,-207360,286208,-48640,-35328,-552448,436224,64512]),(⟨0,2,3⟩,[0,0,0,-4096,46080,-190464,322560,-98304,-13312,-788480,726016]),(⟨0,2,5⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨0,3,0⟩,[1024,-23296,226304,-1253120,4356608,-9672192,13305344,-11384320,11599360,-24870656,36257280,-22280960,1248256]),(⟨0,3,1⟩,[0,-4608,77568,-551168,2146816,-4924928,6598656,-5530624,7413248,-17401856,23249152,-13169408]),(⟨0,3,2⟩,[-768,15872,-124416,494592,-1061376,1089536,-339968,566272,-2138880,1995264,290304]),(⟨0,3,3⟩,[0,6144,-79360,409088,-1043968,1250816,-573952,997888,-3185152,3267072]),(⟨0,3,5⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨0,4,0⟩,[0,-6656,109312,-760576,2903552,-6517248,8552448,-7090176,9353728,-21711872,29166848,-16620800]),(⟨0,4,1⟩,[0,0,0,0,-12288,180224,-798720,983040,1536000,-5226496,4386816]),(⟨0,5,0⟩,[-1280,26112,-210432,890368,-2105856,2501120,-932864,975360,-5521664,6223872,-9728]),(⟨0,5,1⟩,[0,3072,-43520,242176,-654848,810496,-267776,470528,-2654720,3143168]),(⟨0,5,2⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨0,5,3⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨0,6,0⟩,[0,9216,-122880,651264,-1698816,2061312,-841728,1468416,-5839872,6410240]),(⟨0,6,1⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨0,7,0⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨0,8,0⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨1,0,0⟩,[-256,6400,-71168,468992,-2033152,6035712,-12416000,17950208,-20158720,24111360,-35897856,47958528,-44517376,23203072,-3591168]),(⟨1,0,1⟩,[0,1536,-29440,245248,-1167360,3503360,-6918656,9406464,-10592256,14870528,-24656640,31963648,-26578944,11001088]),(⟨1,0,2⟩,[256,-5888,54016,-266240,780800,-1393152,1513472,-1217536,1474304,-2322176,2612480,-1397760,-225792]),(⟨1,0,3⟩,[0,-2048,31232,-199680,690688,-1384960,1675776,-1617408,2319872,-3708416,4211712,-2541056]),(⟨1,0,5⟩,[0,3072,-43520,242176,-654848,810496,-267776,470528,-2654720,3143168]),(⟨1,0,6⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨1,1,0⟩,[0,3072,-58880,490496,-2334720,7006720,-13837312,18812928,-21184512,29741056,-49313280,63927296,-53157888,22002176]),(⟨1,1,1⟩,[0,0,0,0,8192,-139264,819200,-2007040,1146880,4431872,-11272192,12787712,-6823936]),(⟨1,1,5⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨1,2,0⟩,[256,-5888,54016,-263168,738304,-1177088,1026048,-755712,969472,632064,-6148864,10793984,-6780928]),(⟨1,2,1⟩,[0,0,0,0,0,0,8192,-106496,344064,49152,-1269760,974848]),(⟨1,3,0⟩,[0,-6656,108800,-750848,2837504,-6309888,8274432,-7148032,9733120,-21110272,27460864,-15710464]),(⟨1,3,1⟩,[0,0,0,0,-12288,180224,-798720,983040,1536000,-5226496,4386816]),(⟨1,4,0⟩,[0,0,0,0,-12288,180224,-798720,983040,1536000,-5226496,4386816]),(⟨1,5,0⟩,[0,3072,-43520,242176,-654848,810496,-267776,470528,-2654720,3143168]),(⟨1,5,1⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨1,6,0⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨2,0,0⟩,[0,1536,-29952,256000,-1263616,3989248,-8409088,12099072,-13109760,16293376,-28533504,40350208,-32622080,12027136]),(⟨2,0,1⟩,[0,0,0,3072,-42496,216064,-487424,461824,-504832,2954240,-8761344,12191744,-6555136]),(⟨2,0,2⟩,[0,0,512,-9728,66048,-207360,286208,-48640,-35328,-552448,436224,64512]),(⟨2,0,3⟩,[0,0,0,-4096,46080,-190464,322560,-98304,-13312,-788480,726016]),(⟨2,0,5⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨2,1,0⟩,[256,-5888,54016,-263168,738304,-1177088,1026048,-755712,969472,632064,-6148864,10793984,-6780928]),(⟨2,1,1⟩,[0,0,0,0,0,0,8192,-106496,344064,49152,-1269760,974848]),(⟨2,2,0⟩,[0,0,1024,-19456,132096,-414720,572416,-97280,-70656,-1104896,872448,129024]),(⟨2,2,7⟩,[-2048,24576,-61440,-73728,243712]),(⟨2,3,0⟩,[-768,15872,-124416,490496,-1015296,899072,-17408,467968,-2152192,1206784,1016320]),(⟨2,3,2⟩,[-1024,17408,-102400,250880,-143360,-553984,1409024,-1598464,852992]),(⟨2,4,2⟩,[0,0,-2048,26624,-86016,-12288,317440,-243712]),(⟨2,5,0⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨2,5,2⟩,[3072,-45056,199680,-245760,-384000,1306624,-1096704]),(⟨2,7,2⟩,[-2048,24576,-61440,-73728,243712]),(⟨3,0,0⟩,[1024,-23296,226304,-1253120,4356608,-9672192,13305344,-11384320,11599360,-24870656,36257280,-22280960,1248256]),(⟨3,0,1⟩,[0,-4608,77568,-551168,2146816,-4924928,6598656,-5530624,7413248,-17401856,23249152,-13169408]),(⟨3,0,2⟩,[-768,15872,-124416,494592,-1061376,1089536,-339968,566272,-2138880,1995264,290304]),(⟨3,0,3⟩,[0,6144,-79360,409088,-1043968,1250816,-573952,997888,-3185152,3267072]),(⟨3,0,5⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨3,1,0⟩,[0,-6656,108800,-750848,2837504,-6309888,8274432,-7148032,9733120,-21110272,27460864,-15710464]),(⟨3,1,1⟩,[0,0,0,0,-12288,180224,-798720,983040,1536000,-5226496,4386816]),(⟨3,2,0⟩,[-768,15872,-124416,490496,-1015296,899072,-17408,467968,-2152192,1206784,1016320]),(⟨3,2,2⟩,[-1024,17408,-102400,250880,-143360,-553984,1409024,-1598464,852992]),(⟨3,3,0⟩,[0,12288,-158720,818176,-2087936,2501632,-1147904,1995776,-6370304,6534144]),(⟨3,5,0⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨4,0,0⟩,[0,-6656,109312,-760576,2903552,-6517248,8552448,-7090176,9353728,-21711872,29166848,-16620800]),(⟨4,0,1⟩,[0,0,0,0,-12288,180224,-798720,983040,1536000,-5226496,4386816]),(⟨4,1,0⟩,[0,0,0,0,-12288,180224,-798720,983040,1536000,-5226496,4386816]),(⟨4,2,2⟩,[0,0,-2048,26624,-86016,-12288,317440,-243712]),(⟨5,0,0⟩,[-1280,26112,-210432,890368,-2105856,2501120,-932864,975360,-5521664,6223872,-9728]),(⟨5,0,1⟩,[0,3072,-43520,242176,-654848,810496,-267776,470528,-2654720,3143168]),(⟨5,0,2⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨5,0,3⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨5,1,0⟩,[0,3072,-43520,242176,-654848,810496,-267776,470528,-2654720,3143168]),(⟨5,1,1⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨5,2,0⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨5,2,2⟩,[3072,-45056,199680,-245760,-384000,1306624,-1096704]),(⟨5,3,0⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨6,0,0⟩,[0,9216,-122880,651264,-1698816,2061312,-841728,1468416,-5839872,6410240]),(⟨6,0,1⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨6,1,0⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨7,0,0⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨7,2,2⟩,[-2048,24576,-61440,-73728,243712]),(⟨8,0,0⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,0⟩,[0,-3,15,-21,3,6]),(⟨0,0,1⟩,[1,-5,10,-11,7]),(⟨0,0,2⟩,[0,0,2,-2]),(⟨0,0,3⟩,[-3,8,-9])]

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,768,-19200,211200,-1353216,5551872,-14879232,25181184,-24884736,17603328,-34691328,72561408,-63906816,8190720,13512192,-3078144]),(⟨0,0,1⟩,[-256,6400,-75776,557312,-2755072,9295872,-21142016,31539200,-31638784,33685248,-63433728,99309312,-80091136,19953664,5838336]),(⟨0,0,2⟩,[0,768,-12288,96256,-514048,2047744,-5883904,11194368,-13132800,12629248,-23420928,40431616,-34221056,11833600]),(⟨0,0,3⟩,[1024,-23296,232448,-1346816,4937216,-11493888,16107008,-12834304,12176896,-30335744,44201472,-23182592,-929792]),(⟨0,0,4⟩,[0,-6656,109312,-760576,2903552,-6517248,8552448,-7090176,9353728,-21711872,29166848,-16620800]),(⟨0,0,5⟩,[-1280,26112,-210432,890368,-2105856,2501120,-932864,975360,-5521664,6223872,-9728]),(⟨0,0,6⟩,[0,9216,-122880,651264,-1698816,2061312,-841728,1468416,-5839872,6410240]),(⟨0,0,7⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨0,0,8⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨0,1,0⟩,[-256,6400,-75776,557312,-2755072,9295872,-21142016,31539200,-31638784,33685248,-63433728,99309312,-80091136,19953664,5838336]),(⟨0,1,1⟩,[0,3072,-58880,490496,-2334720,6994432,-13628416,17620992,-18739200,30711808,-59647488,75342848,-53735424,19077632]),(⟨0,1,2⟩,[256,-5888,54016,-263168,738304,-1177088,1026048,-755712,969472,632064,-6148864,10793984,-6780928]),(⟨0,1,3⟩,[0,-6656,108800,-750848,2837504,-6309888,8274432,-7148032,9733120,-21110272,27460864,-15710464]),(⟨0,1,4⟩,[0,0,0,0,-12288,180224,-798720,983040,1536000,-5226496,4386816]),(⟨0,1,5⟩,[0,3072,-43520,242176,-654848,810496,-267776,470528,-2654720,3143168]),(⟨0,1,6⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨0,2,0⟩,[0,768,-12288,96256,-514048,2047744,-5883904,11194368,-13132800,12629248,-23420928,40431616,-34221056,11833600]),(⟨0,2,1⟩,[256,-5888,54016,-263168,738304,-1177088,1026048,-755712,969472,632064,-6148864,10793984,-6780928]),(⟨0,2,2⟩,[0,0,1024,-19456,132096,-414720,572416,-97280,-70656,-1104896,872448,129024]),(⟨0,2,3⟩,[-768,15872,-124416,490496,-1015296,899072,-17408,467968,-2152192,1206784,1016320]),(⟨0,2,5⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨0,3,0⟩,[1024,-23296,232448,-1346816,4937216,-11493888,16107008,-12834304,12176896,-30335744,44201472,-23182592,-929792]),(⟨0,3,1⟩,[0,-6656,108800,-750848,2837504,-6309888,8274432,-7148032,9733120,-21110272,27460864,-15710464]),(⟨0,3,2⟩,[-768,15872,-124416,490496,-1015296,899072,-17408,467968,-2152192,1206784,1016320]),(⟨0,3,3⟩,[0,12288,-158720,818176,-2087936,2501632,-1147904,1995776,-6370304,6534144]),(⟨0,3,5⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨0,4,0⟩,[0,-6656,109312,-760576,2903552,-6517248,8552448,-7090176,9353728,-21711872,29166848,-16620800]),(⟨0,4,1⟩,[0,0,0,0,-12288,180224,-798720,983040,1536000,-5226496,4386816]),(⟨0,5,0⟩,[-1280,26112,-210432,890368,-2105856,2501120,-932864,975360,-5521664,6223872,-9728]),(⟨0,5,1⟩,[0,3072,-43520,242176,-654848,810496,-267776,470528,-2654720,3143168]),(⟨0,5,2⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨0,5,3⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨0,6,0⟩,[0,9216,-122880,651264,-1698816,2061312,-841728,1468416,-5839872,6410240]),(⟨0,6,1⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨0,7,0⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨0,8,0⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨1,0,0⟩,[-256,6400,-75776,557312,-2755072,9295872,-21142016,31539200,-31638784,33685248,-63433728,99309312,-80091136,19953664,5838336]),(⟨1,0,1⟩,[0,3072,-58880,490496,-2334720,6994432,-13628416,17620992,-18739200,30711808,-59647488,75342848,-53735424,19077632]),(⟨1,0,2⟩,[256,-5888,54016,-263168,738304,-1177088,1026048,-755712,969472,632064,-6148864,10793984,-6780928]),(⟨1,0,3⟩,[0,-6656,108800,-750848,2837504,-6309888,8274432,-7148032,9733120,-21110272,27460864,-15710464]),(⟨1,0,4⟩,[0,0,0,0,-12288,180224,-798720,983040,1536000,-5226496,4386816]),(⟨1,0,5⟩,[0,3072,-43520,242176,-654848,810496,-267776,470528,-2654720,3143168]),(⟨1,0,6⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨1,1,0⟩,[0,3072,-58880,490496,-2334720,6994432,-13628416,17620992,-18739200,30711808,-59647488,75342848,-53735424,19077632]),(⟨1,1,1⟩,[0,0,0,0,12288,-208896,1228800,-3010560,1720320,6647808,-16908288,19181568,-10235904]),(⟨1,1,2⟩,[0,0,0,0,0,0,8192,-106496,344064,49152,-1269760,974848]),(⟨1,1,3⟩,[0,0,0,0,-12288,180224,-798720,983040,1536000,-5226496,4386816]),(⟨1,1,5⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨1,2,0⟩,[256,-5888,54016,-263168,738304,-1177088,1026048,-755712,969472,632064,-6148864,10793984,-6780928]),(⟨1,2,1⟩,[0,0,0,0,0,0,8192,-106496,344064,49152,-1269760,974848]),(⟨1,3,0⟩,[0,-6656,108800,-750848,2837504,-6309888,8274432,-7148032,9733120,-21110272,27460864,-15710464]),(⟨1,3,1⟩,[0,0,0,0,-12288,180224,-798720,983040,1536000,-5226496,4386816]),(⟨1,4,0⟩,[0,0,0,0,-12288,180224,-798720,983040,1536000,-5226496,4386816]),(⟨1,5,0⟩,[0,3072,-43520,242176,-654848,810496,-267776,470528,-2654720,3143168]),(⟨1,5,1⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨1,6,0⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨2,0,0⟩,[0,768,-12288,96256,-514048,2047744,-5883904,11194368,-13132800,12629248,-23420928,40431616,-34221056,11833600]),(⟨2,0,1⟩,[256,-5888,54016,-263168,738304,-1177088,1026048,-755712,969472,632064,-6148864,10793984,-6780928]),(⟨2,0,2⟩,[0,0,1024,-19456,132096,-414720,572416,-97280,-70656,-1104896,872448,129024]),(⟨2,0,3⟩,[-768,15872,-124416,490496,-1015296,899072,-17408,467968,-2152192,1206784,1016320]),(⟨2,0,5⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨2,1,0⟩,[256,-5888,54016,-263168,738304,-1177088,1026048,-755712,969472,632064,-6148864,10793984,-6780928]),(⟨2,1,1⟩,[0,0,0,0,0,0,8192,-106496,344064,49152,-1269760,974848]),(⟨2,2,0⟩,[0,0,1024,-19456,132096,-414720,572416,-97280,-70656,-1104896,872448,129024]),(⟨2,2,2⟩,[0,3072,-52224,297984,-611328,-242688,2583552,-2853888,144384,731136]),(⟨2,2,3⟩,[-1024,17408,-102400,250880,-143360,-553984,1409024,-1598464,852992]),(⟨2,2,4⟩,[0,0,-2048,26624,-86016,-12288,317440,-243712]),(⟨2,2,5⟩,[3072,-45056,199680,-245760,-384000,1306624,-1096704]),(⟨2,2,7⟩,[-2048,24576,-61440,-73728,243712]),(⟨2,3,0⟩,[-768,15872,-124416,490496,-1015296,899072,-17408,467968,-2152192,1206784,1016320]),(⟨2,3,2⟩,[-1024,17408,-102400,250880,-143360,-553984,1409024,-1598464,852992]),(⟨2,4,2⟩,[0,0,-2048,26624,-86016,-12288,317440,-243712]),(⟨2,5,0⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨2,5,2⟩,[3072,-45056,199680,-245760,-384000,1306624,-1096704]),(⟨2,7,2⟩,[-2048,24576,-61440,-73728,243712]),(⟨3,0,0⟩,[1024,-23296,232448,-1346816,4937216,-11493888,16107008,-12834304,12176896,-30335744,44201472,-23182592,-929792]),(⟨3,0,1⟩,[0,-6656,108800,-750848,2837504,-6309888,8274432,-7148032,9733120,-21110272,27460864,-15710464]),(⟨3,0,2⟩,[-768,15872,-124416,490496,-1015296,899072,-17408,467968,-2152192,1206784,1016320]),(⟨3,0,3⟩,[0,12288,-158720,818176,-2087936,2501632,-1147904,1995776,-6370304,6534144]),(⟨3,0,5⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨3,1,0⟩,[0,-6656,108800,-750848,2837504,-6309888,8274432,-7148032,9733120,-21110272,27460864,-15710464]),(⟨3,1,1⟩,[0,0,0,0,-12288,180224,-798720,983040,1536000,-5226496,4386816]),(⟨3,2,0⟩,[-768,15872,-124416,490496,-1015296,899072,-17408,467968,-2152192,1206784,1016320]),(⟨3,2,2⟩,[-1024,17408,-102400,250880,-143360,-553984,1409024,-1598464,852992]),(⟨3,3,0⟩,[0,12288,-158720,818176,-2087936,2501632,-1147904,1995776,-6370304,6534144]),(⟨3,5,0⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨4,0,0⟩,[0,-6656,109312,-760576,2903552,-6517248,8552448,-7090176,9353728,-21711872,29166848,-16620800]),(⟨4,0,1⟩,[0,0,0,0,-12288,180224,-798720,983040,1536000,-5226496,4386816]),(⟨4,1,0⟩,[0,0,0,0,-12288,180224,-798720,983040,1536000,-5226496,4386816]),(⟨4,2,2⟩,[0,0,-2048,26624,-86016,-12288,317440,-243712]),(⟨5,0,0⟩,[-1280,26112,-210432,890368,-2105856,2501120,-932864,975360,-5521664,6223872,-9728]),(⟨5,0,1⟩,[0,3072,-43520,242176,-654848,810496,-267776,470528,-2654720,3143168]),(⟨5,0,2⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨5,0,3⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨5,1,0⟩,[0,3072,-43520,242176,-654848,810496,-267776,470528,-2654720,3143168]),(⟨5,1,1⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨5,2,0⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨5,2,2⟩,[3072,-45056,199680,-245760,-384000,1306624,-1096704]),(⟨5,3,0⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨6,0,0⟩,[0,9216,-122880,651264,-1698816,2061312,-841728,1468416,-5839872,6410240]),(⟨6,0,1⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨6,1,0⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨7,0,0⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨7,2,2⟩,[-2048,24576,-61440,-73728,243712]),(⟨8,0,0⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016])]


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
    (Poly.add (Poly.scale (K.ofRat r432) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 1 13).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r430*r431 : ℚ)=r432 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 1 13 r430 r431 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 1=13 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 1 13).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C071

#print axioms Coulomb8.Columns.C071.sound
