import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C118

def r0 : ℚ := { num := -8192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 260096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -30720, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 30470144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -170270720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 682446848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -292179968, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 4703305728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -8361476096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 1604012032, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -10566060032, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 5897850880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -191725568, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 97386496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -2048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := 135168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := -2729984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 4022272, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -179081216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 45654016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -348418048, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 5780684800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -1496242176, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 14084657152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -12788713472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 6313779200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -815169536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 18432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -520192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 5965824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -36802560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 135426048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -301596672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 331853824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 2113536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -1884698624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 3982127104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -4182718464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 241577984, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 6144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -20480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 5924864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -48775168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 234844160, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -740909056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 1656705024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -385794048, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 2962552832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -1576652800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -69613568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -10240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 227328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -1441792, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -32768, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 39219200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -28356608, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 562937856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -1107673088, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 1377433600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -772630528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -4096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 212992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -3014656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 18169856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -56729600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 111919104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -157188096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 89374720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := 9195520, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 32768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -786432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 6062080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -1310720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 7503872, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -96468992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 94470144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := 40960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := -1331200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := 17055744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := -120528896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := 548708352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := -1781612544, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := 4402110464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := -8342528000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 664420352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -9360797696, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := 3469565952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 2048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -8192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 2463744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := -2850816, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 91049984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -262324224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 28979200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -68124672, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -16209920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 1384243200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -171997184, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -61440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 1703936, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -17252352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 90177536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -42426368, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 721813504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -1297563648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := 12058624, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -703918080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 253952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -2596864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 679936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -30826496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 91594752, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -230285312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 13377536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -4096, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 741376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -7364608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 35905536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -92389376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 118423552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -12034048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := -188801024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 140128256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 17551360, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := 262144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -3964928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := 24870912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := -77438976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 7667712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -107413504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -48529408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 23678976, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 8192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -188416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := 1482752, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := -4218880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -237568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 18046976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := -2351104, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -57344, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := -65536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := 983040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -4325376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := 3538944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 14876672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -196608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 81920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := -1933312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := 14860288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := -52232192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := 6209536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := -163414016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := 155795456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := -16384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 483328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := -6115328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := 43876352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -28475392, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 619757568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -1468309504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 2986115072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := -5034196992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := 5640151040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := -171151360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := 8192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := -1867776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := 13549568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -61284352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 183173120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -56098816, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 735920128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -1150046208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := 7348224, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 20480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -524288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := 5226496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := -26214400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 74047488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -136052736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 206290944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -264503296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := 10309632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := -253952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := 2859008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := -15491072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 48128000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := -105750528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := 170778624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -7872512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := 49152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := -884736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := 5259264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := -9764864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -12238848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := 3047424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := -19808256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -262144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 16384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -360448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 2736128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -7667712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := 507904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 1736704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := 360448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := -2736128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := 7667712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -507904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -1736704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 24576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -565248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := 4448256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -12656640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -712704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 54140928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -7053312, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -172032, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 130048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := -15360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 15235072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -85135360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := 341223424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := -146089984, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := 2351652864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -4180738048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 802006016, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -5283030016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 2948925440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -95862784, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 48693248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -1024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := 67584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := -1364992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := 2011136, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -89540608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := 22827008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -174209024, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 2890342400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -748121088, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := 7042328576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := -6394356736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := 3156889600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -407584768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 9216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -260096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := 2982912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -18401280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := 67713024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := -150798336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := 165926912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := 1056768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := -942349312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := 1991063552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := -2091359232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := 120788992, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 3072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -10240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := 2962432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -24387584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := 117422080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -370454528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 828352512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -192897024, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := 1481276416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := -788326400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := -34806784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -5120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := 113664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := -720896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := -16384, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := 19609600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := -14178304, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 281468928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -553836544, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 688716800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := -386315264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 106496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := -1507328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := 9084928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := -28364800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := 55959552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := -78594048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := 44687360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 4597760, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -393216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := 3031040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := -655360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := 3751936, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := -48234496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := 47235072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := -665600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := 8527872, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := -60264448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := 274354176, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := -890806272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := 2201055232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := -4171264000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := 332210176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -4680398848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := 1734782976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := 1024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := -4096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := 1231872, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -1425408, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 45524992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := -131162112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := 14489600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := -34062336, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -8104960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 692121600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -85998592, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := -30720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := 851968, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := -8626176, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := 45088768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := -21213184, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := 360906752, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := -648781824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 6029312, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := -351959040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := 126976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := -1298432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := 339968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := -15413248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := 45797376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -115142656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 6688768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -2048, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 370688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := -3682304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 17952768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -46194688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 59211776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -6017024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := -94400512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := 70064128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 8775680, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := 131072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := -1982464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := 12435456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := -38719488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := 3833856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := -53706752, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := -24264704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := 11839488, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 4096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -94208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := -2109440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := -118784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := 9023488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := -1175552, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := -28672, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := -32768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := 491520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := -2162688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := 1769472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := 7438336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := -98304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -966656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 7430144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := -26116096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := 3104768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := -81707008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := 77897728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := 241664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := -3057664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := 21938176, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -14237696, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := 309878784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := -734154752, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := 1493057536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := -2517098496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := 2820075520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := -85575680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := 4096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := -933888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := 6774784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := -30642176, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := 91586560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := -28049408, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := 367960064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := -575023104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := 3674112, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := 10240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := -262144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := 2613248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := -13107200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := 37023744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := -68026368, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := 103145472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := -132251648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := 5154816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := -126976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := 1429504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := -7745536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := 24064000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := -52875264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := 85389312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := -3936256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := -442368, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := 2629632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := -4882432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := -6119424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := 1523712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := -9904128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := -131072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := -180224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := 1368064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := -3833856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := 868352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := 180224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := -1368064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := 3833856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := -868352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := 12288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := -282624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := 2224128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := -6328320, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := -356352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := 27070464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := -3526656, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := -86016, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := 1, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := 1, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13],[r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26],[r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38],[r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49],[r50,r51,r52,r53,r54,r55,r56,r57,r58,r59],[r60,r61,r62,r63,r64,r65,r66,r67,r68],[0,r69,r70,r71,r72,r73,r74,r75],[],[],[],[],[],[],[0,r76,r77,r78,r79,r80,r81,r82,r83,r84,r85,r86],[r87,r88,r89,r90,r91,r92,r93,r94,r95,r96,r97],[0,r98,r99,r100,r101,r102,r103,r104,r105,r106],[0,r0,r107,r108,r109,r110,r111,r112,r113],[],[],[],[],[],[],[],[r114,r115,r116,r117,r118,r119,r120,r121,r122,r123],[r60,r124,r125,r126,r127,r128,r129,r130,r131],[r132,r133,r134,r135,r136,r137,r138,r139],[0,r140,r141,r142,r143,r144,r145],[],[],[],[],[],[0,r146,r147,r148,r149,r150,r151,r152],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[r153,r154,r155,r156,r157,r158,r159,r160,r161,r162,r163],[r60,r164,r165,r166,r167,r168,r169,r170,r171,r172],[r173,r174,r175,r176,r177,r178,r179,r180,r181],[r132,r182,r183,r184,r185,r186,r187,r188],[],[],[],[],[],[],[0,r189,r190,r191,r192,r193,r194,r195,r196],[0,r197,r198,r199,r200,r201,r202,-16384],[],[],[],[],[],[],[r153,r203,r204,r205,r206,r207,16384],[],[],[],[],[],[],[],[],[],[],[],[r208,r209,r210,r211,r212,r213,r214,r215],[0,r140,r141,r142,r143,r144,r145],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[r60,r216,r217,r218,r219,r220,r221,r222,r223,r224,r225,r226,r227,r228]),(⟨0,0,1⟩,[r229,r230,r231,r232,r233,r234,r235,r236,r237,r238,r239,r240,r241]),(⟨0,0,2⟩,[r242,r243,r244,r245,r246,r247,r248,r249,r250,r251,r252,r253]),(⟨0,0,3⟩,[r254,r255,r256,r257,r258,r259,r260,r261,r262,r263,r264]),(⟨0,0,4⟩,[r265,r266,r267,r268,r269,r270,r271,r272,r273,r274]),(⟨0,0,5⟩,[r14,r275,r276,r277,r278,r279,r280,r281,r282]),(⟨0,0,6⟩,[0,r197,r283,r284,r285,r286,r287,r288]),(⟨0,1,0⟩,[r229,r230,r231,r232,r233,r234,r235,r236,r237,r238,r239,r240,r241]),(⟨0,1,1⟩,[0,r173,r289,r290,r291,r292,r293,r294,r295,r296,r297,r298]),(⟨0,1,2⟩,[r299,r300,r301,r302,r303,r304,r305,r306,r307,r308,r309]),(⟨0,1,3⟩,[0,r310,r311,r312,r313,r314,r315,r316,r317,r318]),(⟨0,1,4⟩,[0,r60,r319,r320,r321,r322,r323,r324,r325]),(⟨0,2,0⟩,[r242,r243,r244,r245,r246,r247,r248,r249,r250,r251,r252,r253]),(⟨0,2,1⟩,[r299,r300,r301,r302,r303,r304,r305,r306,r307,r308,r309]),(⟨0,2,2⟩,[r326,r327,r328,r329,r330,r331,r332,r333,r334,r335]),(⟨0,2,3⟩,[r14,r336,r337,r338,r339,r340,r341,r342,r343]),(⟨0,2,4⟩,[r344,r345,r115,r346,r347,r348,r349,r350]),(⟨0,2,5⟩,[0,r351,r352,r353,r354,r355,r356]),(⟨0,3,0⟩,[r254,r255,r256,r257,r258,r259,r260,r261,r262,r263,r264]),(⟨0,3,1⟩,[0,r310,r311,r312,r313,r314,r315,r316,r317,r318]),(⟨0,3,2⟩,[r14,r336,r337,r338,r339,r340,r341,r342,r343]),(⟨0,3,3⟩,[0,r76,r357,r358,r359,r360,r361,r362]),(⟨0,4,0⟩,[r265,r266,r267,r268,r269,r270,r271,r272,r273,r274]),(⟨0,4,1⟩,[0,r60,r319,r320,r321,r322,r323,r324,r325]),(⟨0,4,2⟩,[r344,r345,r115,r346,r347,r348,r349,r350]),(⟨0,5,0⟩,[r14,r275,r276,r277,r278,r279,r280,r281,r282]),(⟨0,5,2⟩,[0,r351,r352,r353,r354,r355,r356]),(⟨0,6,0⟩,[0,r197,r283,r284,r285,r286,r287,r288]),(⟨1,0,0⟩,[r229,r230,r231,r232,r233,r234,r235,r236,r237,r238,r239,r240,r241]),(⟨1,0,1⟩,[0,r173,r289,r290,r291,r292,r293,r294,r295,r296,r297,r298]),(⟨1,0,2⟩,[r299,r300,r301,r302,r303,r304,r305,r306,r307,r308,r309]),(⟨1,0,3⟩,[0,r310,r311,r312,r313,r314,r315,r316,r317,r318]),(⟨1,0,4⟩,[0,r60,r319,r320,r321,r322,r323,r324,r325]),(⟨1,1,0⟩,[0,r173,r289,r290,r291,r292,r293,r294,r295,r296,r297,r298]),(⟨1,1,1⟩,[r0,r363,r364,r365,r366,r367,r368,r369,r370,r371,r372]),(⟨1,1,2⟩,[r14,r373,r374,r375,r376,r377,r378,r379,r380,r381]),(⟨1,1,3⟩,[r382,r383,r384,r385,r386,r387,r388,r389,r390]),(⟨1,1,4⟩,[r344,r391,r392,r393,r394,r395,r396,r397]),(⟨1,2,0⟩,[r299,r300,r301,r302,r303,r304,r305,r306,r307,r308,r309]),(⟨1,2,1⟩,[r14,r373,r374,r375,r376,r377,r378,r379,r380,r381]),(⟨1,2,2⟩,[0,r208,r398,r399,r400,r401,r402,r403,r404]),(⟨1,2,3⟩,[0,r132,r405,r406,r407,r107,r408,-8192]),(⟨1,3,0⟩,[0,r310,r311,r312,r313,r314,r315,r316,r317,r318]),(⟨1,3,1⟩,[r382,r383,r384,r385,r386,r387,r388,r389,r390]),(⟨1,3,2⟩,[0,r132,r405,r406,r407,r107,r408,-8192]),(⟨1,3,3⟩,[r0,r409,r410,r411,r182,r412,8192]),(⟨1,4,0⟩,[0,r60,r319,r320,r321,r322,r323,r324,r325]),(⟨1,4,1⟩,[r344,r391,r392,r393,r394,r395,r396,r397]),(⟨2,0,0⟩,[r242,r243,r244,r245,r246,r247,r248,r249,r250,r251,r252,r253]),(⟨2,0,1⟩,[r299,r300,r301,r302,r303,r304,r305,r306,r307,r308,r309]),(⟨2,0,2⟩,[r326,r327,r328,r329,r330,r331,r332,r333,r334,r335]),(⟨2,0,3⟩,[r14,r336,r337,r338,r339,r340,r341,r342,r343]),(⟨2,0,4⟩,[r344,r345,r115,r346,r347,r348,r349,r350]),(⟨2,0,5⟩,[0,r351,r352,r353,r354,r355,r356]),(⟨2,1,0⟩,[r299,r300,r301,r302,r303,r304,r305,r306,r307,r308,r309]),(⟨2,1,1⟩,[r14,r373,r374,r375,r376,r377,r378,r379,r380,r381]),(⟨2,1,2⟩,[0,r208,r398,r399,r400,r401,r402,r403,r404]),(⟨2,1,3⟩,[0,r132,r405,r406,r407,r107,r408,-8192]),(⟨2,2,0⟩,[r326,r327,r328,r329,r330,r331,r332,r333,r334,r335]),(⟨2,2,1⟩,[0,r208,r398,r399,r400,r401,r402,r403,r404]),(⟨2,2,2⟩,[r413,r414,r415,r416,r417,r418,r419,r420]),(⟨2,2,3⟩,[0,r351,r352,r353,r354,r355,r356]),(⟨2,3,0⟩,[r14,r336,r337,r338,r339,r340,r341,r342,r343]),(⟨2,3,1⟩,[0,r132,r405,r406,r407,r107,r408,-8192]),(⟨2,3,2⟩,[0,r351,r352,r353,r354,r355,r356]),(⟨2,4,0⟩,[r344,r345,r115,r346,r347,r348,r349,r350]),(⟨2,5,0⟩,[0,r351,r352,r353,r354,r355,r356]),(⟨3,0,0⟩,[r254,r255,r256,r257,r258,r259,r260,r261,r262,r263,r264]),(⟨3,0,1⟩,[0,r310,r311,r312,r313,r314,r315,r316,r317,r318]),(⟨3,0,2⟩,[r14,r336,r337,r338,r339,r340,r341,r342,r343]),(⟨3,0,3⟩,[0,r76,r357,r358,r359,r360,r361,r362]),(⟨3,1,0⟩,[0,r310,r311,r312,r313,r314,r315,r316,r317,r318]),(⟨3,1,1⟩,[r382,r383,r384,r385,r386,r387,r388,r389,r390]),(⟨3,1,2⟩,[0,r132,r405,r406,r407,r107,r408,-8192]),(⟨3,1,3⟩,[r0,r409,r410,r411,r182,r412,8192]),(⟨3,2,0⟩,[r14,r336,r337,r338,r339,r340,r341,r342,r343]),(⟨3,2,1⟩,[0,r132,r405,r406,r407,r107,r408,-8192]),(⟨3,2,2⟩,[0,r351,r352,r353,r354,r355,r356]),(⟨3,3,0⟩,[0,r76,r357,r358,r359,r360,r361,r362]),(⟨3,3,1⟩,[r0,r409,r410,r411,r182,r412,8192]),(⟨4,0,0⟩,[r265,r266,r267,r268,r269,r270,r271,r272,r273,r274]),(⟨4,0,1⟩,[0,r60,r319,r320,r321,r322,r323,r324,r325]),(⟨4,0,2⟩,[r344,r345,r115,r346,r347,r348,r349,r350]),(⟨4,1,0⟩,[0,r60,r319,r320,r321,r322,r323,r324,r325]),(⟨4,1,1⟩,[r344,r391,r392,r393,r394,r395,r396,r397]),(⟨4,2,0⟩,[r344,r345,r115,r346,r347,r348,r349,r350]),(⟨5,0,0⟩,[r14,r275,r276,r277,r278,r279,r280,r281,r282]),(⟨5,0,2⟩,[0,r351,r352,r353,r354,r355,r356]),(⟨5,2,0⟩,[0,r351,r352,r353,r354,r355,r356]),(⟨6,0,0⟩,[0,r197,r283,r284,r285,r286,r287,r288])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[-256,4800,-35712,145856,-387968,744000,-1039488,811328,-95104]),(⟨0,0,1⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨0,0,2⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨0,0,3⟩,[128,-2688,15616,-40192,84608,-123008]),(⟨0,1,0⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨0,1,1⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨0,2,0⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨0,2,2⟩,[-256,3072,-7680,-9216,30464]),(⟨0,3,0⟩,[128,-2688,15616,-40192,84608,-123008]),(⟨1,0,0⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨1,0,1⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨1,1,0⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨2,0,0⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨2,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨2,2,0⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[128,-2688,15616,-40192,84608,-123008])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[16,-208,1008,-2480,2688,-512]),(⟨0,0,1⟩,[0,-96,704,-1760,1664]),(⟨0,0,2⟩,[-16,176,-304,-112]),(⟨0,0,3⟩,[0,128,-384]),(⟨0,1,0⟩,[0,-96,704,-1760,1664]),(⟨0,1,1⟩,[0,-32,320,-544]),(⟨0,2,0⟩,[-16,176,-304,-112]),(⟨0,3,0⟩,[0,128,-384]),(⟨1,0,0⟩,[0,-96,704,-1760,1664]),(⟨1,0,1⟩,[0,-32,320,-544]),(⟨1,1,0⟩,[0,-32,320,-544]),(⟨1,1,1⟩,[32,-320,544]),(⟨2,0,0⟩,[-16,176,-304,-112]),(⟨3,0,0⟩,[0,128,-384])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 6 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r421) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 10 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r422) sourceRight))).isZero := by decide +kernel

noncomputable def partial16 : Poly := []

theorem partial_sound16 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 16)
      sourceRight).eval u v t=partial16.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨2,0,0⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨2,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨2,2,0⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[128,-2688,15616,-40192,84608,-123008])]

noncomputable def partial12 : Poly := [(⟨2,0,0⟩,[5120,-144384,1712128,-11411456,48334848,-138553344,275783680,-378535936,321930240,-78906368,-98312192,24543232]),(⟨2,0,1⟩,[0,-30720,692224,-6254592,30535680,-92004352,184832000,-249630720,192958464,-14886912,-79765504]),(⟨2,0,2⟩,[-9216,236544,-2351104,11583488,-30279680,38246400,4997120,-94887936,107858944,-10228736]),(⟨2,0,3⟩,[0,65536,-1220608,8241152,-25845760,37847040,-10838016,-52183040,69099520]),(⟨2,0,4⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨2,0,5⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨2,1,0⟩,[0,-30720,692224,-6254592,30535680,-92004352,184832000,-249630720,192958464,-14886912,-79765504]),(⟨2,1,1⟩,[0,-10240,258048,-2486272,11808768,-31244288,52613120,-57348096,17108992,26077184]),(⟨2,1,2⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨2,1,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨2,2,0⟩,[-9216,236544,-2351104,11583488,-30279680,38246400,4997120,-94887936,107858944,-10228736]),(⟨2,2,1⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨2,2,2⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨2,2,3⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨2,3,0⟩,[0,65536,-1220608,8241152,-25845760,37847040,-10838016,-52183040,69099520]),(⟨2,3,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨2,3,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨2,4,0⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨2,5,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨3,0,0⟩,[2048,-100352,1630208,-13172736,63000576,-198103040,438730752,-699482112,746022912,-388851712,-16785408]),(⟨3,0,1⟩,[0,-22528,606208,-6103040,31604736,-99618816,220708864,-359735296,374390784,-178608128]),(⟨3,0,2⟩,[-2048,90112,-1236992,7544832,-23228416,36544512,-17981440,-41033728,64468992]),(⟨3,0,3⟩,[0,24576,-573440,4399104,-14974976,26517504,-33472512,30662656]),(⟨3,1,0⟩,[0,-22528,606208,-6103040,31604736,-99618816,220708864,-359735296,374390784,-178608128]),(⟨3,1,1⟩,[10240,-262144,2613248,-13238272,38989824,-76677120,110223360,-102498304,40839168]),(⟨3,1,2⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,1,3⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨3,2,0⟩,[-2048,90112,-1236992,7544832,-23228416,36544512,-17981440,-41033728,64468992]),(⟨3,2,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,3,0⟩,[0,24576,-573440,4399104,-14974976,26517504,-33472512,30662656]),(⟨3,3,1⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨4,0,0⟩,[-5120,121856,-983040,2785280,3160064,-41936896,141746176,-300883968,378534912,-199316480]),(⟨4,0,1⟩,[0,-4096,126976,-1429504,7745536,-24064000,52875264,-85389312,66916352]),(⟨4,0,2⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨4,1,0⟩,[0,-4096,126976,-1429504,7745536,-24064000,52875264,-85389312,66916352]),(⟨4,1,1⟩,[4096,-126976,1429504,-7745536,24064000,-52875264,85389312,-66916352]),(⟨4,2,0⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨5,0,0⟩,[-2048,106496,-1507328,9084928,-28364800,55959552,-78594048,44687360,32184320]),(⟨5,0,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨5,2,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨6,0,0⟩,[0,16384,-393216,3031040,-11141120,26263552,-48234496,47235072])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial16)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 16))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound16 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨0,3,0⟩,[128,-2688,15616,-40192,84608,-123008]),(⟨1,0,0⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨1,0,1⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨1,1,0⟩,[0,0,1024,-12288,30720,36864,-121856])]

noncomputable def partial8 : Poly := [(⟨0,3,0⟩,[2048,-69632,937984,-6918144,32464896,-106098688,253898752,-449851392,553064448,-373964800,62980096]),(⟨0,3,1⟩,[0,-12288,348160,-3616768,19795968,-68374528,168095744,-302387200,357281792,-204685312]),(⟨0,3,2⟩,[-2048,65536,-761856,4194304,-12873728,27328512,-42868736,27918336,13776896]),(⟨0,3,3⟩,[0,16384,-393216,3031040,-11141120,26263552,-48234496,47235072]),(⟨0,4,0⟩,[0,-12288,348160,-3616768,19795968,-68374528,168095744,-302387200,357281792,-204685312]),(⟨0,4,1⟩,[0,-4096,126976,-1429504,7745536,-24064000,52875264,-85389312,66916352]),(⟨0,5,0⟩,[-2048,65536,-761856,4194304,-12873728,27328512,-42868736,27918336,13776896]),(⟨0,6,0⟩,[0,16384,-393216,3031040,-11141120,26263552,-48234496,47235072]),(⟨1,0,0⟩,[-1024,43008,-723968,6819840,-41523200,177291264,-558778368,1341247488,-2472141824,3394508800,-3169758208,1639456768,-249331712]),(⟨1,0,1⟩,[0,6144,-206848,2650112,-18739200,87556096,-304463872,835710976,-1766658048,2602493952,-2277513216,872718336]),(⟨1,0,2⟩,[1024,-40960,619520,-4898816,23939072,-80084992,186828800,-268910592,132690944,200056832,-257309696]),(⟨1,0,3⟩,[0,-8192,245760,-2523136,13484032,-48873472,140197888,-289046528,343097344,-173350912]),(⟨1,0,4⟩,[0,0,0,131072,-1966080,8650752,-7077888,-29753344,46792704]),(⟨1,1,0⟩,[0,6144,-206848,2650112,-18739200,87556096,-304463872,835710976,-1766658048,2602493952,-2277513216,872718336]),(⟨1,1,1⟩,[0,2048,-79872,978944,-5148672,14123008,-42500096,206376960,-662532096,1058568192,-670451712]),(⟨1,1,2⟩,[0,0,-16384,344064,-2244608,2965504,15810560,-37109760,-26132480,79937536]),(⟨1,1,3⟩,[0,0,0,131072,-1966080,8650752,-7077888,-29753344,46792704]),(⟨1,2,0⟩,[1024,-40960,619520,-4898816,23939072,-80084992,186828800,-268910592,132690944,200056832,-257309696]),(⟨1,2,1⟩,[0,0,-16384,344064,-2244608,2965504,15810560,-37109760,-26132480,79937536]),(⟨1,3,0⟩,[0,-20480,593920,-6139904,33280000,-117248000,308293632,-591433728,700379136,-378036224]),(⟨1,3,1⟩,[0,-4096,126976,-1298432,5779456,-15413248,45797376,-115142656,113709056]),(⟨1,4,0⟩,[0,-4096,126976,-1298432,5779456,-15413248,45797376,-115142656,113709056]),(⟨1,4,1⟩,[4096,-126976,1429504,-7745536,24064000,-52875264,85389312,-66916352]),(⟨2,0,0⟩,[5120,-138240,1488896,-8351744,25516032,-30271488,-83255296,504410112,-1319341056,2138022912,-2029402112,834871296]),(⟨2,0,1⟩,[0,-28672,612352,-5177344,23486464,-64479232,100913152,-6389760,-370024448,767873024,-547448832]),(⟨2,0,2⟩,[-9216,236544,-2351104,11550720,-29558784,32774144,20332544,-95903744,48811008,56060928]),(⟨2,0,3⟩,[0,65536,-1220608,8241152,-25845760,37847040,-10838016,-52183040,69099520]),(⟨2,0,4⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨2,0,5⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨2,1,0⟩,[0,-28672,612352,-5177344,23486464,-64479232,100913152,-6389760,-370024448,767873024,-547448832]),(⟨2,1,1⟩,[-2048,69632,-917504,6397952,-27676672,83148800,-196820992,404054016,-607938560,423571456]),(⟨2,1,2⟩,[0,24576,-442368,2629632,-4882432,-6119424,25903104,-9904128,-15597568]),(⟨2,1,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨2,2,0⟩,[-9216,236544,-2351104,11550720,-29558784,32774144,20332544,-95903744,48811008,56060928]),(⟨2,2,1⟩,[0,24576,-442368,2629632,-4882432,-6119424,25903104,-9904128,-15597568]),(⟨2,2,2⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨2,2,3⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨2,3,0⟩,[-2048,131072,-1982464,12435456,-38719488,65175552,-53706752,-24264704,82876416]),(⟨2,3,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨2,3,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨2,4,0⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨2,5,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨3,0,0⟩,[3072,-141312,2249728,-17973248,85039104,-264785920,584140800,-931528704,978263040,-464603136,-71326720]),(⟨3,0,1⟩,[0,-22528,589824,-5726208,28639232,-91181056,221184000,-395829248,407306240,-164960256]),(⟨3,0,2⟩,[-2048,90112,-1236992,7544832,-23228416,36544512,-17981440,-41033728,64468992]),(⟨3,0,3⟩,[0,24576,-573440,4399104,-14974976,26517504,-33472512,30662656]),(⟨3,1,0⟩,[0,-22528,589824,-5726208,28639232,-91181056,221184000,-395829248,407306240,-164960256]),(⟨3,1,1⟩,[10240,-262144,2613248,-13238272,38989824,-76677120,110223360,-102498304,40839168]),(⟨3,1,2⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,1,3⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨3,2,0⟩,[-2048,90112,-1236992,7544832,-23228416,36544512,-17981440,-41033728,64468992]),(⟨3,2,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,3,0⟩,[0,40960,-966656,7430144,-26116096,52781056,-81707008,77897728]),(⟨3,3,1⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨4,0,0⟩,[-5120,113664,-720896,-114688,19609600,-99248128,281468928,-553836544,688716800,-386315264]),(⟨4,0,1⟩,[0,-4096,126976,-1298432,5779456,-15413248,45797376,-115142656,113709056]),(⟨4,0,2⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨4,1,0⟩,[0,-4096,126976,-1298432,5779456,-15413248,45797376,-115142656,113709056]),(⟨4,1,1⟩,[4096,-126976,1429504,-7745536,24064000,-52875264,85389312,-66916352]),(⟨4,2,0⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨5,0,0⟩,[-2048,106496,-1507328,9084928,-28364800,55959552,-78594048,44687360,32184320]),(⟨5,0,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨5,2,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨6,0,0⟩,[0,16384,-393216,3031040,-11141120,26263552,-48234496,47235072])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,1,0⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨0,1,1⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨0,2,0⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨0,2,2⟩,[-256,3072,-7680,-9216,30464])]

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[-1024,43008,-723968,6819840,-41523200,177291264,-558778368,1341247488,-2472141824,3394508800,-3169758208,1639456768,-249331712]),(⟨0,1,1⟩,[0,6144,-206848,2650112,-18739200,87556096,-304463872,835710976,-1766658048,2602493952,-2277513216,872718336]),(⟨0,1,2⟩,[1024,-40960,619520,-4898816,23939072,-80084992,186828800,-268910592,132690944,200056832,-257309696]),(⟨0,1,3⟩,[0,-8192,245760,-2523136,13484032,-48873472,140197888,-289046528,343097344,-173350912]),(⟨0,1,4⟩,[0,0,0,131072,-1966080,8650752,-7077888,-29753344,46792704]),(⟨0,2,0⟩,[5120,-138240,1488896,-8351744,25516032,-30271488,-83255296,504410112,-1319341056,2138022912,-2029402112,834871296]),(⟨0,2,1⟩,[0,-28672,612352,-5177344,23486464,-64479232,100913152,-6389760,-370024448,767873024,-547448832]),(⟨0,2,2⟩,[-9216,236544,-2351104,11550720,-29558784,32774144,20332544,-95903744,48811008,56060928]),(⟨0,2,3⟩,[0,65536,-1220608,8241152,-25845760,37847040,-10838016,-52183040,69099520]),(⟨0,2,4⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨0,2,5⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨0,3,0⟩,[3072,-141312,2249728,-17973248,85039104,-264785920,584140800,-931528704,978263040,-464603136,-71326720]),(⟨0,3,1⟩,[0,-22528,589824,-5726208,28639232,-91181056,221184000,-395829248,407306240,-164960256]),(⟨0,3,2⟩,[-2048,90112,-1236992,7544832,-23228416,36544512,-17981440,-41033728,64468992]),(⟨0,3,3⟩,[0,24576,-573440,4399104,-14974976,26517504,-33472512,30662656]),(⟨0,4,0⟩,[-5120,113664,-720896,-114688,19609600,-99248128,281468928,-553836544,688716800,-386315264]),(⟨0,4,1⟩,[0,-4096,126976,-1298432,5779456,-15413248,45797376,-115142656,113709056]),(⟨0,4,2⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨0,5,0⟩,[-2048,106496,-1507328,9084928,-28364800,55959552,-78594048,44687360,32184320]),(⟨0,5,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨0,6,0⟩,[0,16384,-393216,3031040,-11141120,26263552,-48234496,47235072]),(⟨1,0,0⟩,[-1024,43008,-723968,6819840,-41523200,177291264,-558778368,1341247488,-2472141824,3394508800,-3169758208,1639456768,-249331712]),(⟨1,0,1⟩,[0,6144,-206848,2650112,-18739200,87556096,-304463872,835710976,-1766658048,2602493952,-2277513216,872718336]),(⟨1,0,2⟩,[1024,-40960,619520,-4898816,23939072,-80084992,186828800,-268910592,132690944,200056832,-257309696]),(⟨1,0,3⟩,[0,-8192,245760,-2523136,13484032,-48873472,140197888,-289046528,343097344,-173350912]),(⟨1,0,4⟩,[0,0,0,131072,-1966080,8650752,-7077888,-29753344,46792704]),(⟨1,1,0⟩,[0,12288,-430080,5709824,-41558016,195837952,-663502848,1718657024,-3407929344,4819423232,-4208603136,1683046400]),(⟨1,1,1⟩,[0,4096,-159744,2056192,-12197888,41648128,-126418944,449617920,-1225515008,1841328128,-1138135040]),(⟨1,1,2⟩,[0,0,-16384,311296,-1523712,-2506752,31145984,-38125568,-85180416,146227200]),(⟨1,1,3⟩,[0,0,0,131072,-1966080,8650752,-7077888,-29753344,46792704]),(⟨1,2,0⟩,[1024,-69632,1231872,-9977856,45524992,-131162112,246323200,-238436352,-137784320,692121600,-601990144]),(⟨1,2,1⟩,[-2048,69632,-933888,6774784,-30642176,91586560,-196345856,367960064,-575023104,437219328]),(⟨1,2,2⟩,[0,24576,-442368,2629632,-4882432,-6119424,25903104,-9904128,-15597568]),(⟨1,2,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨1,3,0⟩,[0,-30720,851968,-8626176,45088768,-148492288,360906752,-648781824,717488128,-351959040]),(⟨1,3,1⟩,[10240,-262144,2613248,-13107200,37023744,-68026368,103145472,-132251648,87631872]),(⟨1,3,2⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨1,3,3⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨1,4,0⟩,[0,-4096,126976,-1298432,5779456,-15413248,45797376,-115142656,113709056]),(⟨1,4,1⟩,[4096,-126976,1429504,-7745536,24064000,-52875264,85389312,-66916352]),(⟨2,0,0⟩,[5120,-138240,1488896,-8351744,25516032,-30271488,-83255296,504410112,-1319341056,2138022912,-2029402112,834871296]),(⟨2,0,1⟩,[0,-28672,612352,-5177344,23486464,-64479232,100913152,-6389760,-370024448,767873024,-547448832]),(⟨2,0,2⟩,[-9216,236544,-2351104,11550720,-29558784,32774144,20332544,-95903744,48811008,56060928]),(⟨2,0,3⟩,[0,65536,-1220608,8241152,-25845760,37847040,-10838016,-52183040,69099520]),(⟨2,0,4⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨2,0,5⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨2,1,0⟩,[1024,-69632,1231872,-9977856,45524992,-131162112,246323200,-238436352,-137784320,692121600,-601990144]),(⟨2,1,1⟩,[-2048,69632,-933888,6774784,-30642176,91586560,-196345856,367960064,-575023104,437219328]),(⟨2,1,2⟩,[0,24576,-442368,2629632,-4882432,-6119424,25903104,-9904128,-15597568]),(⟨2,1,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨2,2,0⟩,[-14336,370688,-3682304,17952768,-46194688,59211776,-6017024,-94400512,70064128,61429760]),(⟨2,2,1⟩,[0,24576,-442368,2629632,-4882432,-6119424,25903104,-9904128,-15597568]),(⟨2,2,2⟩,[12288,-282624,2224128,-6328320,-356352,27070464,-24686592,-10235904]),(⟨2,2,3⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨2,3,0⟩,[-2048,131072,-1982464,12435456,-38719488,65175552,-53706752,-24264704,82876416]),(⟨2,3,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨2,3,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨2,4,0⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨2,5,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨3,0,0⟩,[3072,-141312,2249728,-17973248,85039104,-264785920,584140800,-931528704,978263040,-464603136,-71326720]),(⟨3,0,1⟩,[0,-22528,589824,-5726208,28639232,-91181056,221184000,-395829248,407306240,-164960256]),(⟨3,0,2⟩,[-2048,90112,-1236992,7544832,-23228416,36544512,-17981440,-41033728,64468992]),(⟨3,0,3⟩,[0,24576,-573440,4399104,-14974976,26517504,-33472512,30662656]),(⟨3,1,0⟩,[0,-30720,851968,-8626176,45088768,-148492288,360906752,-648781824,717488128,-351959040]),(⟨3,1,1⟩,[10240,-262144,2613248,-13107200,37023744,-68026368,103145472,-132251648,87631872]),(⟨3,1,2⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,1,3⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨3,2,0⟩,[-2048,131072,-1982464,12435456,-38719488,65175552,-53706752,-24264704,82876416]),(⟨3,2,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,2,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨3,3,0⟩,[0,40960,-966656,7430144,-26116096,52781056,-81707008,77897728]),(⟨3,3,1⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨4,0,0⟩,[-5120,113664,-720896,-114688,19609600,-99248128,281468928,-553836544,688716800,-386315264]),(⟨4,0,1⟩,[0,-4096,126976,-1298432,5779456,-15413248,45797376,-115142656,113709056]),(⟨4,0,2⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨4,1,0⟩,[0,-4096,126976,-1298432,5779456,-15413248,45797376,-115142656,113709056]),(⟨4,1,1⟩,[4096,-126976,1429504,-7745536,24064000,-52875264,85389312,-66916352]),(⟨4,2,0⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨5,0,0⟩,[-2048,106496,-1507328,9084928,-28364800,55959552,-78594048,44687360,32184320]),(⟨5,0,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨5,2,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨6,0,0⟩,[0,16384,-393216,3031040,-11141120,26263552,-48234496,47235072])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,0⟩,[-256,4800,-35712,145856,-387968,744000,-1039488,811328,-95104]),(⟨0,0,1⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨0,0,2⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨0,0,3⟩,[128,-2688,15616,-40192,84608,-123008])]

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[-4096,130048,-1827840,15235072,-85135360,341223424,-1022629888,2351652864,-4180738048,5614042112,-5283030016,2948925440,-671039488,48693248]),(⟨0,0,1⟩,[-1024,67584,-1364992,14077952,-89540608,388059136,-1219463168,2890342400,-5236847616,7042328576,-6394356736,3156889600,-407584768]),(⟨0,0,2⟩,[9216,-260096,2982912,-18401280,67713024,-150798336,165926912,125755392,-942349312,1991063552,-2091359232,845522944]),(⟨0,0,3⟩,[3072,-174080,2962432,-24387584,117422080,-370454528,828352512,-1350279168,1481276416,-788326400,-34806784]),(⟨0,0,4⟩,[-5120,113664,-720896,-114688,19609600,-99248128,281468928,-553836544,688716800,-386315264]),(⟨0,0,5⟩,[-2048,106496,-1507328,9084928,-28364800,55959552,-78594048,44687360,32184320]),(⟨0,0,6⟩,[0,16384,-393216,3031040,-11141120,26263552,-48234496,47235072]),(⟨0,1,0⟩,[-1024,67584,-1364992,14077952,-89540608,388059136,-1219463168,2890342400,-5236847616,7042328576,-6394356736,3156889600,-407584768]),(⟨0,1,1⟩,[0,20480,-665600,8527872,-60264448,274354176,-890806272,2201055232,-4171264000,5647572992,-4680398848,1734782976]),(⟨0,1,2⟩,[1024,-69632,1231872,-9977856,45524992,-131162112,246323200,-238436352,-137784320,692121600,-601990144]),(⟨0,1,3⟩,[0,-30720,851968,-8626176,45088768,-148492288,360906752,-648781824,717488128,-351959040]),(⟨0,1,4⟩,[0,-4096,126976,-1298432,5779456,-15413248,45797376,-115142656,113709056]),(⟨0,2,0⟩,[9216,-260096,2982912,-18401280,67713024,-150798336,165926912,125755392,-942349312,1991063552,-2091359232,845522944]),(⟨0,2,1⟩,[1024,-69632,1231872,-9977856,45524992,-131162112,246323200,-238436352,-137784320,692121600,-601990144]),(⟨0,2,2⟩,[-14336,370688,-3682304,17952768,-46194688,59211776,-6017024,-94400512,70064128,61429760]),(⟨0,2,3⟩,[-2048,131072,-1982464,12435456,-38719488,65175552,-53706752,-24264704,82876416]),(⟨0,2,4⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨0,2,5⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨0,3,0⟩,[3072,-174080,2962432,-24387584,117422080,-370454528,828352512,-1350279168,1481276416,-788326400,-34806784]),(⟨0,3,1⟩,[0,-30720,851968,-8626176,45088768,-148492288,360906752,-648781824,717488128,-351959040]),(⟨0,3,2⟩,[-2048,131072,-1982464,12435456,-38719488,65175552,-53706752,-24264704,82876416]),(⟨0,3,3⟩,[0,40960,-966656,7430144,-26116096,52781056,-81707008,77897728]),(⟨0,4,0⟩,[-5120,113664,-720896,-114688,19609600,-99248128,281468928,-553836544,688716800,-386315264]),(⟨0,4,1⟩,[0,-4096,126976,-1298432,5779456,-15413248,45797376,-115142656,113709056]),(⟨0,4,2⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨0,5,0⟩,[-2048,106496,-1507328,9084928,-28364800,55959552,-78594048,44687360,32184320]),(⟨0,5,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨0,6,0⟩,[0,16384,-393216,3031040,-11141120,26263552,-48234496,47235072]),(⟨1,0,0⟩,[-1024,67584,-1364992,14077952,-89540608,388059136,-1219463168,2890342400,-5236847616,7042328576,-6394356736,3156889600,-407584768]),(⟨1,0,1⟩,[0,20480,-665600,8527872,-60264448,274354176,-890806272,2201055232,-4171264000,5647572992,-4680398848,1734782976]),(⟨1,0,2⟩,[1024,-69632,1231872,-9977856,45524992,-131162112,246323200,-238436352,-137784320,692121600,-601990144]),(⟨1,0,3⟩,[0,-30720,851968,-8626176,45088768,-148492288,360906752,-648781824,717488128,-351959040]),(⟨1,0,4⟩,[0,-4096,126976,-1298432,5779456,-15413248,45797376,-115142656,113709056]),(⟨1,1,0⟩,[0,20480,-665600,8527872,-60264448,274354176,-890806272,2201055232,-4171264000,5647572992,-4680398848,1734782976]),(⟨1,1,1⟩,[-8192,241664,-3057664,21938176,-99663872,309878784,-734154752,1493057536,-2517098496,2820075520,-1454786560]),(⟨1,1,2⟩,[-2048,69632,-933888,6774784,-30642176,91586560,-196345856,367960064,-575023104,437219328]),(⟨1,1,3⟩,[10240,-262144,2613248,-13107200,37023744,-68026368,103145472,-132251648,87631872]),(⟨1,1,4⟩,[4096,-126976,1429504,-7745536,24064000,-52875264,85389312,-66916352]),(⟨1,2,0⟩,[1024,-69632,1231872,-9977856,45524992,-131162112,246323200,-238436352,-137784320,692121600,-601990144]),(⟨1,2,1⟩,[-2048,69632,-933888,6774784,-30642176,91586560,-196345856,367960064,-575023104,437219328]),(⟨1,2,2⟩,[0,24576,-442368,2629632,-4882432,-6119424,25903104,-9904128,-15597568]),(⟨1,2,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨1,3,0⟩,[0,-30720,851968,-8626176,45088768,-148492288,360906752,-648781824,717488128,-351959040]),(⟨1,3,1⟩,[10240,-262144,2613248,-13107200,37023744,-68026368,103145472,-132251648,87631872]),(⟨1,3,2⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨1,3,3⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨1,4,0⟩,[0,-4096,126976,-1298432,5779456,-15413248,45797376,-115142656,113709056]),(⟨1,4,1⟩,[4096,-126976,1429504,-7745536,24064000,-52875264,85389312,-66916352]),(⟨2,0,0⟩,[9216,-260096,2982912,-18401280,67713024,-150798336,165926912,125755392,-942349312,1991063552,-2091359232,845522944]),(⟨2,0,1⟩,[1024,-69632,1231872,-9977856,45524992,-131162112,246323200,-238436352,-137784320,692121600,-601990144]),(⟨2,0,2⟩,[-14336,370688,-3682304,17952768,-46194688,59211776,-6017024,-94400512,70064128,61429760]),(⟨2,0,3⟩,[-2048,131072,-1982464,12435456,-38719488,65175552,-53706752,-24264704,82876416]),(⟨2,0,4⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨2,0,5⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨2,1,0⟩,[1024,-69632,1231872,-9977856,45524992,-131162112,246323200,-238436352,-137784320,692121600,-601990144]),(⟨2,1,1⟩,[-2048,69632,-933888,6774784,-30642176,91586560,-196345856,367960064,-575023104,437219328]),(⟨2,1,2⟩,[0,24576,-442368,2629632,-4882432,-6119424,25903104,-9904128,-15597568]),(⟨2,1,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨2,2,0⟩,[-14336,370688,-3682304,17952768,-46194688,59211776,-6017024,-94400512,70064128,61429760]),(⟨2,2,1⟩,[0,24576,-442368,2629632,-4882432,-6119424,25903104,-9904128,-15597568]),(⟨2,2,2⟩,[12288,-282624,2224128,-6328320,-356352,27070464,-24686592,-10235904]),(⟨2,2,3⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨2,3,0⟩,[-2048,131072,-1982464,12435456,-38719488,65175552,-53706752,-24264704,82876416]),(⟨2,3,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨2,3,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨2,4,0⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨2,5,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨3,0,0⟩,[3072,-174080,2962432,-24387584,117422080,-370454528,828352512,-1350279168,1481276416,-788326400,-34806784]),(⟨3,0,1⟩,[0,-30720,851968,-8626176,45088768,-148492288,360906752,-648781824,717488128,-351959040]),(⟨3,0,2⟩,[-2048,131072,-1982464,12435456,-38719488,65175552,-53706752,-24264704,82876416]),(⟨3,0,3⟩,[0,40960,-966656,7430144,-26116096,52781056,-81707008,77897728]),(⟨3,1,0⟩,[0,-30720,851968,-8626176,45088768,-148492288,360906752,-648781824,717488128,-351959040]),(⟨3,1,1⟩,[10240,-262144,2613248,-13107200,37023744,-68026368,103145472,-132251648,87631872]),(⟨3,1,2⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,1,3⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨3,2,0⟩,[-2048,131072,-1982464,12435456,-38719488,65175552,-53706752,-24264704,82876416]),(⟨3,2,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,2,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨3,3,0⟩,[0,40960,-966656,7430144,-26116096,52781056,-81707008,77897728]),(⟨3,3,1⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨4,0,0⟩,[-5120,113664,-720896,-114688,19609600,-99248128,281468928,-553836544,688716800,-386315264]),(⟨4,0,1⟩,[0,-4096,126976,-1298432,5779456,-15413248,45797376,-115142656,113709056]),(⟨4,0,2⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨4,1,0⟩,[0,-4096,126976,-1298432,5779456,-15413248,45797376,-115142656,113709056]),(⟨4,1,1⟩,[4096,-126976,1429504,-7745536,24064000,-52875264,85389312,-66916352]),(⟨4,2,0⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨5,0,0⟩,[-2048,106496,-1507328,9084928,-28364800,55959552,-78594048,44687360,32184320]),(⟨5,0,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨5,2,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨6,0,0⟩,[0,16384,-393216,3031040,-11141120,26263552,-48234496,47235072])]


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
    (Poly.add (Poly.scale (K.ofRat r423) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 6 10).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r421*r422 : ℚ)=r423 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 6 10 r421 r422 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 6=10 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 6 10).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C118

#print axioms Coulomb8.Columns.C118.sound
