import Coulomb8.HermiteArithmetic
import Coulomb8.HermiteConstruction

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Coulomb8
namespace HermiteArithmetic
open Polynomial

noncomputable def p0 : RealPoly := [v9,v10,v11,v12,v8]
noncomputable def p1 : RealPoly := [v14,v16,v18,v20]
theorem p1_eq : p1=RealPoly.derivative p0 := by
  norm_num [p1,p0,v8,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p2 : RealPoly := [v13]
noncomputable def p3 : RealPoly := [v21,v13]
noncomputable def p4 : RealPoly := [v27,v25]
theorem p4_eq : p4=RealPoly.mul p2 p3 := by
  norm_num [p4,p2,p3,v13,v24,v25,v26,v27,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p5 : RealPoly := [v28,v29]
theorem p5_eq : p5=RealPoly.scale v23 p4 := by
  norm_num [p5,p4,v28,v29,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p6 : RealPoly := [v30,v13]
noncomputable def p7 : RealPoly := [v38,v39,v36]
theorem p7_eq : p7=RealPoly.mul p5 p6 := by
  norm_num [p7,p5,p6,v13,v26,v33,v34,v35,v36,v37,v38,v39,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p8 : RealPoly := [v40,v41,v42]
theorem p8_eq : p8=RealPoly.scale v32 p7 := by
  norm_num [p8,p7,v40,v41,v42,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p9 : RealPoly := [v43,v13]
noncomputable def p10 : RealPoly := [v55,v56,v54,v51]
theorem p10_eq : p10=RealPoly.mul p8 p9 := by
  norm_num [p10,p8,p9,v13,v26,v46,v47,v48,v49,v50,v51,v52,v53,v54,v55,v56,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p11 : RealPoly := [v57,v58,v59,v60]
theorem p11_eq : p11=RealPoly.scale v45 p10 := by
  norm_num [p11,p10,v57,v58,v59,v60,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
theorem eval_p0_v0 : v81=RealPoly.eval p0 v0 := by
  norm_num [p0,v8,v9,v10,v11,v12,v26,v72,v73,v74,v75,v76,v77,v78,v79,v80,v81,RealPoly.eval,RealPoly.toPolynomial]
  all_goals simp [mul_comm]
theorem eval_p1_v0 : v92=RealPoly.eval p1 v0 := by
  norm_num [p1,v26,v72,v86,v87,v88,v89,v90,v91,v92,RealPoly.eval,RealPoly.toPolynomial]
  all_goals simp [mul_comm]
noncomputable def p12 : RealPoly := [v103,v104,v105]
theorem p12_eq : p12=RealPoly.derivative p11 := by
  norm_num [p12,p11,v13,v15,v17,v103,v104,v105,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
theorem eval_p12_v0 : v110=RealPoly.eval p12 v0 := by
  norm_num [p12,v26,v72,v106,v107,v108,v109,v110,RealPoly.eval,RealPoly.toPolynomial]
  all_goals simp [mul_comm]
noncomputable def p13 : RealPoly := [v85]
noncomputable def p14 : RealPoly := [v115,v13]
noncomputable def p15 : RealPoly := [v116,v117]
theorem p15_eq : p15=RealPoly.scale v114 p14 := by
  norm_num [p15,p14,v13,v116,v117,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p16 : RealPoly := [v118,v117]
theorem p16_eq : p16=RealPoly.add p13 p15 := by
  norm_num [p16,p13,p15,v118,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p17 : RealPoly := [v144,v145,v146,v147,v143,v139,v134]
theorem p17_eq : p17=RealPoly.mul p11 p11 := by
  norm_num [p17,p11,p11,v26,v119,v120,v121,v122,v123,v124,v125,v126,v127,v128,v129,v130,v131,v132,v133,v134,v135,v136,v137,v138,v139,v140,v141,v142,v143,v144,v145,v146,v147,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p18 : RealPoly := [v163,v164,v165,v166,v167,v168,v169,v161]
theorem p18_eq : p18=RealPoly.mul p16 p17 := by
  norm_num [p18,p16,p17,v26,v148,v149,v150,v151,v152,v153,v154,v155,v156,v157,v158,v159,v160,v161,v162,v163,v164,v165,v166,v167,v168,v169,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p19 : RealPoly := [v13]
noncomputable def p20 : RealPoly := [v115,v13]
noncomputable def p21 : RealPoly := [v173,v25]
theorem p21_eq : p21=RealPoly.mul p19 p20 := by
  norm_num [p21,p19,p20,v13,v25,v26,v172,v173,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p22 : RealPoly := [v174,v175]
theorem p22_eq : p22=RealPoly.scale v171 p21 := by
  norm_num [p22,p21,v174,v175,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p23 : RealPoly := [v30,v13]
noncomputable def p24 : RealPoly := [v183,v184,v181]
theorem p24_eq : p24=RealPoly.mul p22 p23 := by
  norm_num [p24,p22,p23,v13,v26,v178,v179,v180,v181,v182,v183,v184,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p25 : RealPoly := [v185,v186,v187]
theorem p25_eq : p25=RealPoly.scale v177 p24 := by
  norm_num [p25,p24,v185,v186,v187,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p26 : RealPoly := [v43,v13]
noncomputable def p27 : RealPoly := [v199,v200,v198,v195]
theorem p27_eq : p27=RealPoly.mul p25 p26 := by
  norm_num [p27,p25,p26,v13,v26,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p28 : RealPoly := [v201,v202,v203,v204]
theorem p28_eq : p28=RealPoly.scale v189 p27 := by
  norm_num [p28,p27,v201,v202,v203,v204,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
theorem eval_p0_v1 : v225=RealPoly.eval p0 v1 := by
  norm_num [p0,v8,v9,v10,v11,v12,v26,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,RealPoly.eval,RealPoly.toPolynomial]
  all_goals simp [mul_comm]
theorem eval_p1_v1 : v236=RealPoly.eval p1 v1 := by
  norm_num [p1,v26,v216,v230,v231,v232,v233,v234,v235,v236,RealPoly.eval,RealPoly.toPolynomial]
  all_goals simp [mul_comm]
noncomputable def p29 : RealPoly := [v246,v247,v248]
theorem p29_eq : p29=RealPoly.derivative p28 := by
  norm_num [p29,p28,v13,v15,v17,v246,v247,v248,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
theorem eval_p29_v1 : v253=RealPoly.eval p29 v1 := by
  norm_num [p29,v26,v216,v249,v250,v251,v252,v253,RealPoly.eval,RealPoly.toPolynomial]
  all_goals simp [mul_comm]
noncomputable def p30 : RealPoly := [v229]
noncomputable def p31 : RealPoly := [v21,v13]
noncomputable def p32 : RealPoly := [v258,v259]
theorem p32_eq : p32=RealPoly.scale v257 p31 := by
  norm_num [p32,p31,v13,v258,v259,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p33 : RealPoly := [v260,v259]
theorem p33_eq : p33=RealPoly.add p30 p32 := by
  norm_num [p33,p30,p32,v260,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p34 : RealPoly := [v286,v287,v288,v289,v285,v281,v276]
theorem p34_eq : p34=RealPoly.mul p28 p28 := by
  norm_num [p34,p28,p28,v26,v261,v262,v263,v264,v265,v266,v267,v268,v269,v270,v271,v272,v273,v274,v275,v276,v277,v278,v279,v280,v281,v282,v283,v284,v285,v286,v287,v288,v289,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p35 : RealPoly := [v305,v306,v307,v308,v309,v310,v311,v303]
theorem p35_eq : p35=RealPoly.mul p33 p34 := by
  norm_num [p35,p33,p34,v26,v290,v291,v292,v293,v294,v295,v296,v297,v298,v299,v300,v301,v302,v303,v304,v305,v306,v307,v308,v309,v310,v311,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p36 : RealPoly := [v13]
noncomputable def p37 : RealPoly := [v115,v13]
noncomputable def p38 : RealPoly := [v173,v25]
theorem p38_eq : p38=RealPoly.mul p36 p37 := by
  norm_num [p38,p36,p37,v13,v25,v26,v172,v173,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p39 : RealPoly := [v314,v315]
theorem p39_eq : p39=RealPoly.scale v313 p38 := by
  norm_num [p39,p38,v314,v315,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p40 : RealPoly := [v21,v13]
noncomputable def p41 : RealPoly := [v323,v324,v321]
theorem p41_eq : p41=RealPoly.mul p39 p40 := by
  norm_num [p41,p39,p40,v13,v26,v318,v319,v320,v321,v322,v323,v324,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p42 : RealPoly := [v325,v326,v327]
theorem p42_eq : p42=RealPoly.scale v317 p41 := by
  norm_num [p42,p41,v325,v326,v327,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p43 : RealPoly := [v43,v13]
noncomputable def p44 : RealPoly := [v339,v340,v338,v335]
theorem p44_eq : p44=RealPoly.mul p42 p43 := by
  norm_num [p44,p42,p43,v13,v26,v330,v331,v332,v333,v334,v335,v336,v337,v338,v339,v340,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p45 : RealPoly := [v341,v342,v343,v344]
theorem p45_eq : p45=RealPoly.scale v329 p44 := by
  norm_num [p45,p44,v341,v342,v343,v344,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
theorem eval_p0_v2 : v365=RealPoly.eval p0 v2 := by
  norm_num [p0,v8,v9,v10,v11,v12,v26,v356,v357,v358,v359,v360,v361,v362,v363,v364,v365,RealPoly.eval,RealPoly.toPolynomial]
  all_goals simp [mul_comm]
theorem eval_p1_v2 : v376=RealPoly.eval p1 v2 := by
  norm_num [p1,v26,v356,v370,v371,v372,v373,v374,v375,v376,RealPoly.eval,RealPoly.toPolynomial]
  all_goals simp [mul_comm]
noncomputable def p46 : RealPoly := [v386,v387,v388]
theorem p46_eq : p46=RealPoly.derivative p45 := by
  norm_num [p46,p45,v13,v15,v17,v386,v387,v388,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
theorem eval_p46_v2 : v393=RealPoly.eval p46 v2 := by
  norm_num [p46,v26,v356,v389,v390,v391,v392,v393,RealPoly.eval,RealPoly.toPolynomial]
  all_goals simp [mul_comm]
noncomputable def p47 : RealPoly := [v369]
noncomputable def p48 : RealPoly := [v30,v13]
noncomputable def p49 : RealPoly := [v398,v399]
theorem p49_eq : p49=RealPoly.scale v397 p48 := by
  norm_num [p49,p48,v13,v398,v399,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p50 : RealPoly := [v400,v399]
theorem p50_eq : p50=RealPoly.add p47 p49 := by
  norm_num [p50,p47,p49,v400,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p51 : RealPoly := [v426,v427,v428,v429,v425,v421,v416]
theorem p51_eq : p51=RealPoly.mul p45 p45 := by
  norm_num [p51,p45,p45,v26,v401,v402,v403,v404,v405,v406,v407,v408,v409,v410,v411,v412,v413,v414,v415,v416,v417,v418,v419,v420,v421,v422,v423,v424,v425,v426,v427,v428,v429,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p52 : RealPoly := [v445,v446,v447,v448,v449,v450,v451,v443]
theorem p52_eq : p52=RealPoly.mul p50 p51 := by
  norm_num [p52,p50,p51,v26,v430,v431,v432,v433,v434,v435,v436,v437,v438,v439,v440,v441,v442,v443,v444,v445,v446,v447,v448,v449,v450,v451,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p53 : RealPoly := [v13]
noncomputable def p54 : RealPoly := [v115,v13]
noncomputable def p55 : RealPoly := [v173,v25]
theorem p55_eq : p55=RealPoly.mul p53 p54 := by
  norm_num [p55,p53,p54,v13,v25,v26,v172,v173,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p56 : RealPoly := [v454,v455]
theorem p56_eq : p56=RealPoly.scale v453 p55 := by
  norm_num [p56,p55,v454,v455,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p57 : RealPoly := [v21,v13]
noncomputable def p58 : RealPoly := [v463,v464,v461]
theorem p58_eq : p58=RealPoly.mul p56 p57 := by
  norm_num [p58,p56,p57,v13,v26,v458,v459,v460,v461,v462,v463,v464,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p59 : RealPoly := [v465,v466,v467]
theorem p59_eq : p59=RealPoly.scale v457 p58 := by
  norm_num [p59,p58,v465,v466,v467,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p60 : RealPoly := [v30,v13]
noncomputable def p61 : RealPoly := [v479,v480,v478,v475]
theorem p61_eq : p61=RealPoly.mul p59 p60 := by
  norm_num [p61,p59,p60,v13,v26,v470,v471,v472,v473,v474,v475,v476,v477,v478,v479,v480,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p62 : RealPoly := [v481,v482,v483,v484]
theorem p62_eq : p62=RealPoly.scale v469 p61 := by
  norm_num [p62,p61,v481,v482,v483,v484,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
theorem eval_p0_v3 : v505=RealPoly.eval p0 v3 := by
  norm_num [p0,v8,v9,v10,v11,v12,v26,v496,v497,v498,v499,v500,v501,v502,v503,v504,v505,RealPoly.eval,RealPoly.toPolynomial]
  all_goals simp [mul_comm]
theorem eval_p1_v3 : v516=RealPoly.eval p1 v3 := by
  norm_num [p1,v26,v496,v510,v511,v512,v513,v514,v515,v516,RealPoly.eval,RealPoly.toPolynomial]
  all_goals simp [mul_comm]
noncomputable def p63 : RealPoly := [v526,v527,v528]
theorem p63_eq : p63=RealPoly.derivative p62 := by
  norm_num [p63,p62,v13,v15,v17,v526,v527,v528,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
theorem eval_p63_v3 : v533=RealPoly.eval p63 v3 := by
  norm_num [p63,v26,v496,v529,v530,v531,v532,v533,RealPoly.eval,RealPoly.toPolynomial]
  all_goals simp [mul_comm]
noncomputable def p64 : RealPoly := [v509]
noncomputable def p65 : RealPoly := [v43,v13]
noncomputable def p66 : RealPoly := [v538,v539]
theorem p66_eq : p66=RealPoly.scale v537 p65 := by
  norm_num [p66,p65,v13,v538,v539,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p67 : RealPoly := [v540,v539]
theorem p67_eq : p67=RealPoly.add p64 p66 := by
  norm_num [p67,p64,p66,v540,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p68 : RealPoly := [v566,v567,v568,v569,v565,v561,v556]
theorem p68_eq : p68=RealPoly.mul p62 p62 := by
  norm_num [p68,p62,p62,v26,v541,v542,v543,v544,v545,v546,v547,v548,v549,v550,v551,v552,v553,v554,v555,v556,v557,v558,v559,v560,v561,v562,v563,v564,v565,v566,v567,v568,v569,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p69 : RealPoly := [v585,v586,v587,v588,v589,v590,v591,v583]
theorem p69_eq : p69=RealPoly.mul p67 p68 := by
  norm_num [p69,p67,p68,v26,v570,v571,v572,v573,v574,v575,v576,v577,v578,v579,v580,v581,v582,v583,v584,v585,v586,v587,v588,v589,v590,v591,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p70 : RealPoly := [v26]
noncomputable def p71 : RealPoly := [v592,v164,v165,v166,v167,v168,v169,v161]
theorem p71_eq : p71=RealPoly.add p70 p18 := by
  norm_num [p71,p70,p18,v26,v592,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p72 : RealPoly := [v593,v594,v595,v596,v597,v598,v599,v600]
theorem p72_eq : p72=RealPoly.add p71 p35 := by
  norm_num [p72,p71,p35,v593,v594,v595,v596,v597,v598,v599,v600,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p73 : RealPoly := [v601,v602,v603,v604,v605,v606,v607,v608]
theorem p73_eq : p73=RealPoly.add p72 p52 := by
  norm_num [p73,p72,p52,v601,v602,v603,v604,v605,v606,v607,v608,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p74 : RealPoly := [v609,v610,v611,v612,v613,v614,v615,v616]
theorem p74_eq : p74=RealPoly.add p73 p69 := by
  norm_num [p74,p73,p69,v609,v610,v611,v612,v613,v614,v615,v616,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p75 : RealPoly := [v13,v97,v617,v617,v97,v13]
noncomputable def p76 : RealPoly := [v642,v673,v674,v675,v676,v677,v678,v679,v672,v665,v658,v650,v625]
theorem p76_eq : p76=RealPoly.mul p75 p74 := by
  norm_num [p76,p75,p74,v13,v26,v97,v617,v618,v619,v620,v621,v622,v623,v624,v625,v626,v627,v628,v629,v630,v631,v632,v633,v634,v635,v636,v637,v638,v639,v640,v641,v642,v643,v644,v645,v646,v647,v648,v649,v650,v651,v652,v653,v654,v655,v656,v657,v658,v659,v660,v661,v662,v663,v664,v665,v666,v667,v668,v669,v670,v671,v672,v673,v674,v675,v676,v677,v678,v679,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p77 : RealPoly := [v680,v681,v682,v683,v684,v677,v678,v679,v672,v665,v658,v650,v625]
theorem p77_eq : p77=RealPoly.add p0 p76 := by
  norm_num [p77,p0,p76,v8,v9,v10,v11,v12,v680,v681,v682,v683,v684,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
theorem taylor_model : p0.toPolynomial=taylor4 := by
  apply Polynomial.funext
  intro x
  norm_num [p0,RealPoly.toPolynomial,taylor4,v9,v10,v11,v12,v8]
  <;> ring <;> rfl

theorem lagrange_model0 : p11.toPolynomial=lagrange 0 := by
  have he : (Finset.univ : Finset (Fin 4)).erase 0={1,2,3} := by decide +kernel
  rw [lagrange,Lagrange.basis,he]
  rw [Finset.prod_insert (by decide),Finset.prod_insert (by decide),Finset.prod_singleton]
  simp only [p1_eq,p4_eq,p5_eq,p7_eq,p8_eq,p10_eq,p11_eq,RealPoly.toPolynomial_add,RealPoly.toPolynomial_mul,RealPoly.toPolynomial_scale]
  norm_num [lagrange,Lagrange.basis,Lagrange.basisDivisor,Fin.univ_succ,Finset.prod_insert,Finset.prod_singleton,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,RealPoly.toPolynomial,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31,v32,v33,v34,v35,v36,v37,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47,v48,v49,v50,v51,v52,v53,v54,v55,v56,v57,v58,v59,v60]
  <;> ring <;> rfl

theorem lagrange_model1 : p28.toPolynomial=lagrange 1 := by
  have he : (Finset.univ : Finset (Fin 4)).erase 1={0,2,3} := by decide +kernel
  rw [lagrange,Lagrange.basis,he]
  rw [Finset.prod_insert (by decide),Finset.prod_insert (by decide),Finset.prod_singleton]
  simp only [p1_eq,p4_eq,p5_eq,p7_eq,p8_eq,p10_eq,p11_eq,p12_eq,p15_eq,p16_eq,p17_eq,p18_eq,p21_eq,p22_eq,p24_eq,p25_eq,p27_eq,p28_eq,RealPoly.toPolynomial_add,RealPoly.toPolynomial_mul,RealPoly.toPolynomial_scale]
  norm_num [lagrange,Lagrange.basis,Lagrange.basisDivisor,Fin.univ_succ,Finset.prod_insert,Finset.prod_singleton,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27,p28,RealPoly.toPolynomial,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31,v32,v33,v34,v35,v36,v37,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47,v48,v49,v50,v51,v52,v53,v54,v55,v56,v57,v58,v59,v60,v61,v62,v63,v64,v65,v66,v67,v68,v69,v70,v71,v72,v73,v74,v75,v76,v77,v78,v79,v80,v81,v82,v83,v84,v85,v86,v87,v88,v89,v90,v91,v92,v93,v94,v95,v96,v97,v98,v99,v100,v101,v102,v103,v104,v105,v106,v107,v108,v109,v110,v111,v112,v113,v114,v115,v116,v117,v118,v119,v120,v121,v122,v123,v124,v125,v126,v127,v128,v129,v130,v131,v132,v133,v134,v135,v136,v137,v138,v139,v140,v141,v142,v143,v144,v145,v146,v147,v148,v149,v150,v151,v152,v153,v154,v155,v156,v157,v158,v159,v160,v161,v162,v163,v164,v165,v166,v167,v168,v169,v170,v171,v172,v173,v174,v175,v176,v177,v178,v179,v180,v181,v182,v183,v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204]
  <;> ring <;> rfl

theorem lagrange_model2 : p45.toPolynomial=lagrange 2 := by
  have he : (Finset.univ : Finset (Fin 4)).erase 2={0,1,3} := by decide +kernel
  rw [lagrange,Lagrange.basis,he]
  rw [Finset.prod_insert (by decide),Finset.prod_insert (by decide),Finset.prod_singleton]
  simp only [p1_eq,p4_eq,p5_eq,p7_eq,p8_eq,p10_eq,p11_eq,p12_eq,p15_eq,p16_eq,p17_eq,p18_eq,p21_eq,p22_eq,p24_eq,p25_eq,p27_eq,p28_eq,p29_eq,p32_eq,p33_eq,p34_eq,p35_eq,p38_eq,p39_eq,p41_eq,p42_eq,p44_eq,p45_eq,RealPoly.toPolynomial_add,RealPoly.toPolynomial_mul,RealPoly.toPolynomial_scale]
  norm_num [lagrange,Lagrange.basis,Lagrange.basisDivisor,Fin.univ_succ,Finset.prod_insert,Finset.prod_singleton,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27,p28,p29,p30,p31,p32,p33,p34,p35,p36,p37,p38,p39,p40,p41,p42,p43,p44,p45,RealPoly.toPolynomial,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31,v32,v33,v34,v35,v36,v37,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47,v48,v49,v50,v51,v52,v53,v54,v55,v56,v57,v58,v59,v60,v61,v62,v63,v64,v65,v66,v67,v68,v69,v70,v71,v72,v73,v74,v75,v76,v77,v78,v79,v80,v81,v82,v83,v84,v85,v86,v87,v88,v89,v90,v91,v92,v93,v94,v95,v96,v97,v98,v99,v100,v101,v102,v103,v104,v105,v106,v107,v108,v109,v110,v111,v112,v113,v114,v115,v116,v117,v118,v119,v120,v121,v122,v123,v124,v125,v126,v127,v128,v129,v130,v131,v132,v133,v134,v135,v136,v137,v138,v139,v140,v141,v142,v143,v144,v145,v146,v147,v148,v149,v150,v151,v152,v153,v154,v155,v156,v157,v158,v159,v160,v161,v162,v163,v164,v165,v166,v167,v168,v169,v170,v171,v172,v173,v174,v175,v176,v177,v178,v179,v180,v181,v182,v183,v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253,v254,v255,v256,v257,v258,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v269,v270,v271,v272,v273,v274,v275,v276,v277,v278,v279,v280,v281,v282,v283,v284,v285,v286,v287,v288,v289,v290,v291,v292,v293,v294,v295,v296,v297,v298,v299,v300,v301,v302,v303,v304,v305,v306,v307,v308,v309,v310,v311,v312,v313,v314,v315,v316,v317,v318,v319,v320,v321,v322,v323,v324,v325,v326,v327,v328,v329,v330,v331,v332,v333,v334,v335,v336,v337,v338,v339,v340,v341,v342,v343,v344]
  <;> ring <;> rfl

theorem lagrange_model3 : p62.toPolynomial=lagrange 3 := by
  have he : (Finset.univ : Finset (Fin 4)).erase 3={0,1,2} := by decide +kernel
  rw [lagrange,Lagrange.basis,he]
  rw [Finset.prod_insert (by decide),Finset.prod_insert (by decide),Finset.prod_singleton]
  simp only [p1_eq,p4_eq,p5_eq,p7_eq,p8_eq,p10_eq,p11_eq,p12_eq,p15_eq,p16_eq,p17_eq,p18_eq,p21_eq,p22_eq,p24_eq,p25_eq,p27_eq,p28_eq,p29_eq,p32_eq,p33_eq,p34_eq,p35_eq,p38_eq,p39_eq,p41_eq,p42_eq,p44_eq,p45_eq,p46_eq,p49_eq,p50_eq,p51_eq,p52_eq,p55_eq,p56_eq,p58_eq,p59_eq,p61_eq,p62_eq,RealPoly.toPolynomial_add,RealPoly.toPolynomial_mul,RealPoly.toPolynomial_scale]
  norm_num [lagrange,Lagrange.basis,Lagrange.basisDivisor,Fin.univ_succ,Finset.prod_insert,Finset.prod_singleton,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27,p28,p29,p30,p31,p32,p33,p34,p35,p36,p37,p38,p39,p40,p41,p42,p43,p44,p45,p46,p47,p48,p49,p50,p51,p52,p53,p54,p55,p56,p57,p58,p59,p60,p61,p62,RealPoly.toPolynomial,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31,v32,v33,v34,v35,v36,v37,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47,v48,v49,v50,v51,v52,v53,v54,v55,v56,v57,v58,v59,v60,v61,v62,v63,v64,v65,v66,v67,v68,v69,v70,v71,v72,v73,v74,v75,v76,v77,v78,v79,v80,v81,v82,v83,v84,v85,v86,v87,v88,v89,v90,v91,v92,v93,v94,v95,v96,v97,v98,v99,v100,v101,v102,v103,v104,v105,v106,v107,v108,v109,v110,v111,v112,v113,v114,v115,v116,v117,v118,v119,v120,v121,v122,v123,v124,v125,v126,v127,v128,v129,v130,v131,v132,v133,v134,v135,v136,v137,v138,v139,v140,v141,v142,v143,v144,v145,v146,v147,v148,v149,v150,v151,v152,v153,v154,v155,v156,v157,v158,v159,v160,v161,v162,v163,v164,v165,v166,v167,v168,v169,v170,v171,v172,v173,v174,v175,v176,v177,v178,v179,v180,v181,v182,v183,v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253,v254,v255,v256,v257,v258,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v269,v270,v271,v272,v273,v274,v275,v276,v277,v278,v279,v280,v281,v282,v283,v284,v285,v286,v287,v288,v289,v290,v291,v292,v293,v294,v295,v296,v297,v298,v299,v300,v301,v302,v303,v304,v305,v306,v307,v308,v309,v310,v311,v312,v313,v314,v315,v316,v317,v318,v319,v320,v321,v322,v323,v324,v325,v326,v327,v328,v329,v330,v331,v332,v333,v334,v335,v336,v337,v338,v339,v340,v341,v342,v343,v344,v345,v346,v347,v348,v349,v350,v351,v352,v353,v354,v355,v356,v357,v358,v359,v360,v361,v362,v363,v364,v365,v366,v367,v368,v369,v370,v371,v372,v373,v374,v375,v376,v377,v378,v379,v380,v381,v382,v383,v384,v385,v386,v387,v388,v389,v390,v391,v392,v393,v394,v395,v396,v397,v398,v399,v400,v401,v402,v403,v404,v405,v406,v407,v408,v409,v410,v411,v412,v413,v414,v415,v416,v417,v418,v419,v420,v421,v422,v423,v424,v425,v426,v427,v428,v429,v430,v431,v432,v433,v434,v435,v436,v437,v438,v439,v440,v441,v442,v443,v444,v445,v446,v447,v448,v449,v450,v451,v452,v453,v454,v455,v456,v457,v458,v459,v460,v461,v462,v463,v464,v465,v466,v467,v468,v469,v470,v471,v472,v473,v474,v475,v476,v477,v478,v479,v480,v481,v482,v483,v484]
  <;> ring <;> rfl

end HermiteArithmetic
end Coulomb8
