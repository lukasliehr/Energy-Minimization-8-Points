import Coulomb8.CoefficientMatrix.C00
import Coulomb8.CoefficientMatrix.C01
import Coulomb8.CoefficientMatrix.C02
import Coulomb8.CoefficientMatrix.C03
import Coulomb8.CoefficientMatrix.C04
import Coulomb8.CoefficientMatrix.C05
import Coulomb8.CoefficientMatrix.C06
import Coulomb8.CoefficientMatrix.C07
import Coulomb8.CoefficientMatrix.C08
import Coulomb8.CoefficientMatrix.C09
import Coulomb8.CoefficientMatrix.C10
import Coulomb8.CoefficientMatrix.C11
import Coulomb8.CoefficientMatrix.C12
import Coulomb8.CoefficientMatrix.C13
import Coulomb8.CoefficientMatrix.C14
import Coulomb8.CoefficientMatrix.C15
import Coulomb8.CoefficientMatrix.C16
import Coulomb8.CoefficientMatrix.C17
import Coulomb8.CoefficientMatrix.C18
import Coulomb8.CoefficientMatrix.C19
import Coulomb8.CoefficientMatrix.C20
import Coulomb8.CoefficientMatrix.C21
import Coulomb8.CoefficientMatrix.C22
import Coulomb8.CoefficientMatrix.C23

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.CoefficientMatrix

def columns : Fin 192 → Fin 102 → K := ![column0,column1,column2,column3,column4,column5,column6,column7,column8,column9,column10,column11,column12,column13,column14,column15,column16,column17,column18,column19,column20,column21,column22,column23,column24,column25,column26,column27,column28,column29,column30,column31,column32,column33,column34,column35,column36,column37,column38,column39,column40,column41,column42,column43,column44,column45,column46,column47,column48,column49,column50,column51,column52,column53,column54,column55,column56,column57,column58,column59,column60,column61,column62,column63,column64,column65,column66,column67,column68,column69,column70,column71,column72,column73,column74,column75,column76,column77,column78,column79,column80,column81,column82,column83,column84,column85,column86,column87,column88,column89,column90,column91,column92,column93,column94,column95,column96,column97,column98,column99,column100,column101,column102,column103,column104,column105,column106,column107,column108,column109,column110,column111,column112,column113,column114,column115,column116,column117,column118,column119,column120,column121,column122,column123,column124,column125,column126,column127,column128,column129,column130,column131,column132,column133,column134,column135,column136,column137,column138,column139,column140,column141,column142,column143,column144,column145,column146,column147,column148,column149,column150,column151,column152,column153,column154,column155,column156,column157,column158,column159,column160,column161,column162,column163,column164,column165,column166,column167,column168,column169,column170,column171,column172,column173,column174,column175,column176,column177,column178,column179,column180,column181,column182,column183,column184,column185,column186,column187,column188,column189,column190,column191]
def boxes : Fin 192 → Fin 102 → Dyadic := ![boxes0,boxes1,boxes2,boxes3,boxes4,boxes5,boxes6,boxes7,boxes8,boxes9,boxes10,boxes11,boxes12,boxes13,boxes14,boxes15,boxes16,boxes17,boxes18,boxes19,boxes20,boxes21,boxes22,boxes23,boxes24,boxes25,boxes26,boxes27,boxes28,boxes29,boxes30,boxes31,boxes32,boxes33,boxes34,boxes35,boxes36,boxes37,boxes38,boxes39,boxes40,boxes41,boxes42,boxes43,boxes44,boxes45,boxes46,boxes47,boxes48,boxes49,boxes50,boxes51,boxes52,boxes53,boxes54,boxes55,boxes56,boxes57,boxes58,boxes59,boxes60,boxes61,boxes62,boxes63,boxes64,boxes65,boxes66,boxes67,boxes68,boxes69,boxes70,boxes71,boxes72,boxes73,boxes74,boxes75,boxes76,boxes77,boxes78,boxes79,boxes80,boxes81,boxes82,boxes83,boxes84,boxes85,boxes86,boxes87,boxes88,boxes89,boxes90,boxes91,boxes92,boxes93,boxes94,boxes95,boxes96,boxes97,boxes98,boxes99,boxes100,boxes101,boxes102,boxes103,boxes104,boxes105,boxes106,boxes107,boxes108,boxes109,boxes110,boxes111,boxes112,boxes113,boxes114,boxes115,boxes116,boxes117,boxes118,boxes119,boxes120,boxes121,boxes122,boxes123,boxes124,boxes125,boxes126,boxes127,boxes128,boxes129,boxes130,boxes131,boxes132,boxes133,boxes134,boxes135,boxes136,boxes137,boxes138,boxes139,boxes140,boxes141,boxes142,boxes143,boxes144,boxes145,boxes146,boxes147,boxes148,boxes149,boxes150,boxes151,boxes152,boxes153,boxes154,boxes155,boxes156,boxes157,boxes158,boxes159,boxes160,boxes161,boxes162,boxes163,boxes164,boxes165,boxes166,boxes167,boxes168,boxes169,boxes170,boxes171,boxes172,boxes173,boxes174,boxes175,boxes176,boxes177,boxes178,boxes179,boxes180,boxes181,boxes182,boxes183,boxes184,boxes185,boxes186,boxes187,boxes188,boxes189,boxes190,boxes191]
noncomputable def matrix : Matrix (Fin 102) (Fin 192) ℝ := fun r c => K.eval (columns c r)
theorem contains (r : Fin 102) (c : Fin 192) : (boxes c r).Contains (matrix r c) := by
  fin_cases c
  · exact bounds0 r
  · exact bounds1 r
  · exact bounds2 r
  · exact bounds3 r
  · exact bounds4 r
  · exact bounds5 r
  · exact bounds6 r
  · exact bounds7 r
  · exact bounds8 r
  · exact bounds9 r
  · exact bounds10 r
  · exact bounds11 r
  · exact bounds12 r
  · exact bounds13 r
  · exact bounds14 r
  · exact bounds15 r
  · exact bounds16 r
  · exact bounds17 r
  · exact bounds18 r
  · exact bounds19 r
  · exact bounds20 r
  · exact bounds21 r
  · exact bounds22 r
  · exact bounds23 r
  · exact bounds24 r
  · exact bounds25 r
  · exact bounds26 r
  · exact bounds27 r
  · exact bounds28 r
  · exact bounds29 r
  · exact bounds30 r
  · exact bounds31 r
  · exact bounds32 r
  · exact bounds33 r
  · exact bounds34 r
  · exact bounds35 r
  · exact bounds36 r
  · exact bounds37 r
  · exact bounds38 r
  · exact bounds39 r
  · exact bounds40 r
  · exact bounds41 r
  · exact bounds42 r
  · exact bounds43 r
  · exact bounds44 r
  · exact bounds45 r
  · exact bounds46 r
  · exact bounds47 r
  · exact bounds48 r
  · exact bounds49 r
  · exact bounds50 r
  · exact bounds51 r
  · exact bounds52 r
  · exact bounds53 r
  · exact bounds54 r
  · exact bounds55 r
  · exact bounds56 r
  · exact bounds57 r
  · exact bounds58 r
  · exact bounds59 r
  · exact bounds60 r
  · exact bounds61 r
  · exact bounds62 r
  · exact bounds63 r
  · exact bounds64 r
  · exact bounds65 r
  · exact bounds66 r
  · exact bounds67 r
  · exact bounds68 r
  · exact bounds69 r
  · exact bounds70 r
  · exact bounds71 r
  · exact bounds72 r
  · exact bounds73 r
  · exact bounds74 r
  · exact bounds75 r
  · exact bounds76 r
  · exact bounds77 r
  · exact bounds78 r
  · exact bounds79 r
  · exact bounds80 r
  · exact bounds81 r
  · exact bounds82 r
  · exact bounds83 r
  · exact bounds84 r
  · exact bounds85 r
  · exact bounds86 r
  · exact bounds87 r
  · exact bounds88 r
  · exact bounds89 r
  · exact bounds90 r
  · exact bounds91 r
  · exact bounds92 r
  · exact bounds93 r
  · exact bounds94 r
  · exact bounds95 r
  · exact bounds96 r
  · exact bounds97 r
  · exact bounds98 r
  · exact bounds99 r
  · exact bounds100 r
  · exact bounds101 r
  · exact bounds102 r
  · exact bounds103 r
  · exact bounds104 r
  · exact bounds105 r
  · exact bounds106 r
  · exact bounds107 r
  · exact bounds108 r
  · exact bounds109 r
  · exact bounds110 r
  · exact bounds111 r
  · exact bounds112 r
  · exact bounds113 r
  · exact bounds114 r
  · exact bounds115 r
  · exact bounds116 r
  · exact bounds117 r
  · exact bounds118 r
  · exact bounds119 r
  · exact bounds120 r
  · exact bounds121 r
  · exact bounds122 r
  · exact bounds123 r
  · exact bounds124 r
  · exact bounds125 r
  · exact bounds126 r
  · exact bounds127 r
  · exact bounds128 r
  · exact bounds129 r
  · exact bounds130 r
  · exact bounds131 r
  · exact bounds132 r
  · exact bounds133 r
  · exact bounds134 r
  · exact bounds135 r
  · exact bounds136 r
  · exact bounds137 r
  · exact bounds138 r
  · exact bounds139 r
  · exact bounds140 r
  · exact bounds141 r
  · exact bounds142 r
  · exact bounds143 r
  · exact bounds144 r
  · exact bounds145 r
  · exact bounds146 r
  · exact bounds147 r
  · exact bounds148 r
  · exact bounds149 r
  · exact bounds150 r
  · exact bounds151 r
  · exact bounds152 r
  · exact bounds153 r
  · exact bounds154 r
  · exact bounds155 r
  · exact bounds156 r
  · exact bounds157 r
  · exact bounds158 r
  · exact bounds159 r
  · exact bounds160 r
  · exact bounds161 r
  · exact bounds162 r
  · exact bounds163 r
  · exact bounds164 r
  · exact bounds165 r
  · exact bounds166 r
  · exact bounds167 r
  · exact bounds168 r
  · exact bounds169 r
  · exact bounds170 r
  · exact bounds171 r
  · exact bounds172 r
  · exact bounds173 r
  · exact bounds174 r
  · exact bounds175 r
  · exact bounds176 r
  · exact bounds177 r
  · exact bounds178 r
  · exact bounds179 r
  · exact bounds180 r
  · exact bounds181 r
  · exact bounds182 r
  · exact bounds183 r
  · exact bounds184 r
  · exact bounds185 r
  · exact bounds186 r
  · exact bounds187 r
  · exact bounds188 r
  · exact bounds189 r
  · exact bounds190 r
  · exact bounds191 r

end Coulomb8.CoefficientMatrix
