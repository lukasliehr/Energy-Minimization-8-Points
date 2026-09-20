import Coulomb8.QuotientArithmetic

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Coulomb8
namespace QuotientArithmetic
open Polynomial
open scoped BigOperators

noncomputable def p0 : RealPoly := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12]
noncomputable def p1 : RealPoly := [v17]
noncomputable def p2 : RealPoly := [v18,v19]
noncomputable def p3 : RealPoly := [v334,v335,v336,v337,v338,v339,v340,v341,v342,v343,v344,v345,v346,v333,v320,v307,v294,v281,v268,v255,v242,v229,v216,v203,v189]
theorem p3_eq : p3=RealPoly.mul p0 p0 := by
  norm_num [p3,p0,p0,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31,v32,v33,v34,v35,v36,v37,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47,v48,v49,v50,v51,v52,v53,v54,v55,v56,v57,v58,v59,v60,v61,v62,v63,v64,v65,v66,v67,v68,v69,v70,v71,v72,v73,v74,v75,v76,v77,v78,v79,v80,v81,v82,v83,v84,v85,v86,v87,v88,v89,v90,v91,v92,v93,v94,v95,v96,v97,v98,v99,v100,v101,v102,v103,v104,v105,v106,v107,v108,v109,v110,v111,v112,v113,v114,v115,v116,v117,v118,v119,v120,v121,v122,v123,v124,v125,v126,v127,v128,v129,v130,v131,v132,v133,v134,v135,v136,v137,v138,v139,v140,v141,v142,v143,v144,v145,v146,v147,v148,v149,v150,v151,v152,v153,v154,v155,v156,v157,v158,v159,v160,v161,v162,v163,v164,v165,v166,v167,v168,v169,v170,v171,v172,v173,v174,v175,v176,v177,v178,v179,v180,v181,v182,v183,v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253,v254,v255,v256,v257,v258,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v269,v270,v271,v272,v273,v274,v275,v276,v277,v278,v279,v280,v281,v282,v283,v284,v285,v286,v287,v288,v289,v290,v291,v292,v293,v294,v295,v296,v297,v298,v299,v300,v301,v302,v303,v304,v305,v306,v307,v308,v309,v310,v311,v312,v313,v314,v315,v316,v317,v318,v319,v320,v321,v322,v323,v324,v325,v326,v327,v328,v329,v330,v331,v332,v333,v334,v335,v336,v337,v338,v339,v340,v341,v342,v343,v344,v345,v346,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p4 : RealPoly := [v398,v399,v400,v401,v402,v403,v404,v405,v406,v407,v408,v409,v410,v411,v412,v413,v414,v415,v416,v417,v418,v419,v420,v421,v422,v396]
theorem p4_eq : p4=RealPoly.mul p2 p3 := by
  norm_num [p4,p2,p3,v18,v19,v33,v347,v348,v349,v350,v351,v352,v353,v354,v355,v356,v357,v358,v359,v360,v361,v362,v363,v364,v365,v366,v367,v368,v369,v370,v371,v372,v373,v374,v375,v376,v377,v378,v379,v380,v381,v382,v383,v384,v385,v386,v387,v388,v389,v390,v391,v392,v393,v394,v395,v396,v397,v398,v399,v400,v401,v402,v403,v404,v405,v406,v407,v408,v409,v410,v411,v412,v413,v414,v415,v416,v417,v418,v419,v420,v421,v422,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p5 : RealPoly := [v424,v425,v426,v427,v428,v429,v430,v431,v432,v433,v434,v435,v436,v437,v438,v439,v440,v441,v442,v443,v444,v445,v446,v447,v448,v449]
theorem p5_eq : p5=RealPoly.scale v423 p4 := by
  norm_num [p5,p4,v423,v424,v425,v426,v427,v428,v429,v430,v431,v432,v433,v434,v435,v436,v437,v438,v439,v440,v441,v442,v443,v444,v445,v446,v447,v448,v449,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p6 : RealPoly := [v450,v425,v426,v427,v428,v429,v430,v431,v432,v433,v434,v435,v436,v437,v438,v439,v440,v441,v442,v443,v444,v445,v446,v447,v448,v449]
theorem p6_eq : p6=RealPoly.add p1 p5 := by
  norm_num [p6,p1,p5,v17,v450,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p7 : RealPoly := [v17,v451,v452,v452,v451,v17]
noncomputable def p8 : RealPoly := [v453,v17]
noncomputable def p9 : RealPoly := [v459,v460,v457]
theorem p9_eq : p9=RealPoly.mul p8 p8 := by
  norm_num [p9,p8,p8,v17,v33,v454,v455,v456,v457,v458,v459,v460,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p10 : RealPoly := [v470,v481,v482,v480,v478,v476,v473,v463]
theorem p10_eq : p10=RealPoly.mul p7 p9 := by
  norm_num [p10,p7,p9,v17,v33,v451,v452,v461,v462,v463,v464,v465,v466,v467,v468,v469,v470,v471,v472,v473,v474,v475,v476,v477,v478,v479,v480,v481,v482,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p11 : RealPoly := [v483,v17]
noncomputable def p12 : RealPoly := [v488,v489,v457]
theorem p12_eq : p12=RealPoly.mul p11 p11 := by
  norm_num [p12,p11,p11,v17,v33,v457,v484,v485,v486,v487,v488,v489,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p13 : RealPoly := [v533,v534,v535,v532,v529,v526,v523,v520,v517,v513]
theorem p13_eq : p13=RealPoly.mul p10 p12 := by
  norm_num [p13,p10,p12,v33,v490,v491,v492,v493,v494,v495,v496,v497,v498,v499,v500,v501,v502,v503,v504,v505,v506,v507,v508,v509,v510,v511,v512,v513,v514,v515,v516,v517,v518,v519,v520,v521,v522,v523,v524,v525,v526,v527,v528,v529,v530,v531,v532,v533,v534,v535,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p14 : RealPoly := [v536,v17]
noncomputable def p15 : RealPoly := [v541,v542,v457]
theorem p15_eq : p15=RealPoly.mul p14 p14 := by
  norm_num [p15,p14,p14,v17,v33,v457,v537,v538,v539,v540,v541,v542,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p16 : RealPoly := [v598,v599,v600,v597,v594,v591,v588,v585,v582,v579,v576,v572]
theorem p16_eq : p16=RealPoly.mul p13 p15 := by
  norm_num [p16,p13,p15,v33,v543,v544,v545,v546,v547,v548,v549,v550,v551,v552,v553,v554,v555,v556,v557,v558,v559,v560,v561,v562,v563,v564,v565,v566,v567,v568,v569,v570,v571,v572,v573,v574,v575,v576,v577,v578,v579,v580,v581,v582,v583,v584,v585,v586,v587,v588,v589,v590,v591,v592,v593,v594,v595,v596,v597,v598,v599,v600,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p17 : RealPoly := [v601,v17]
noncomputable def p18 : RealPoly := [v606,v607,v457]
theorem p18_eq : p18=RealPoly.mul p17 p17 := by
  norm_num [p18,p17,p17,v17,v33,v457,v602,v603,v604,v605,v606,v607,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p19 : RealPoly := [v675,v676,v677,v674,v671,v668,v665,v662,v659,v656,v653,v650,v647,v643]
theorem p19_eq : p19=RealPoly.mul p16 p18 := by
  norm_num [p19,p16,p18,v33,v608,v609,v610,v611,v612,v613,v614,v615,v616,v617,v618,v619,v620,v621,v622,v623,v624,v625,v626,v627,v628,v629,v630,v631,v632,v633,v634,v635,v636,v637,v638,v639,v640,v641,v642,v643,v644,v645,v646,v647,v648,v649,v650,v651,v652,v653,v654,v655,v656,v657,v658,v659,v660,v661,v662,v663,v664,v665,v666,v667,v668,v669,v670,v671,v672,v673,v674,v675,v676,v677,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p20 : RealPoly := [v675,v676,v677,v674,v671,v668,v665,v662,v659,v656,v653,v650,v647]
noncomputable def p21 : RealPoly := [v33]
noncomputable def p22 : RealPoly := [v450,v425,v426,v427,v428,v429,v430,v431,v432,v433,v434,v435,v436,v437,v438,v439,v440,v441,v442,v443,v444,v445,v446,v447,v448]
noncomputable def p23 : RealPoly := [v33,v33,v33,v33,v33,v33,v33,v33,v33,v33,v33,v33,v675,v676,v677,v674,v671,v668,v665,v662,v659,v656,v653,v650,v647]
theorem p23_eq : p23=List.replicate 12 (0 : ℝ)++p20 := by
  norm_num [p23,p20,v33,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p24 : RealPoly := [v679,v679,v679,v679,v679,v679,v679,v679,v679,v679,v679,v679,v680,v681,v682,v683,v684,v685,v686,v687,v688,v689,v690,v691,v692]
theorem p24_eq : p24=RealPoly.scale v678 p23 := by
  norm_num [p24,p23,v33,v679,v680,v681,v682,v683,v684,v685,v686,v687,v688,v689,v690,v691,v692,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p25 : RealPoly := [v693,v694,v695,v696,v697,v698,v699,v700,v701,v702,v703,v704,v705,v706,v707,v708,v709,v710,v711,v712,v713,v714,v715,v716,v717]
theorem p25_eq : p25=RealPoly.add p22 p24 := by
  norm_num [p25,p22,p24,v693,v694,v695,v696,v697,v698,v699,v700,v701,v702,v703,v704,v705,v706,v707,v708,v709,v710,v711,v712,v713,v714,v715,v716,v717,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p26 : RealPoly := [v33,v33,v33,v33,v33,v33,v33,v33,v33,v33,v33,v33,v449]
noncomputable def p27 : RealPoly := [v718,v33,v33,v33,v33,v33,v33,v33,v33,v33,v33,v33,v449]
theorem p27_eq : p27=RealPoly.add p21 p26 := by
  norm_num [p27,p21,p26,v33,v718,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p28 : RealPoly := [v693,v694,v695,v696,v697,v698,v699,v700,v701,v702,v703,v704,v705,v706,v707,v708,v709,v710,v711,v712,v713,v714,v715,v716]
noncomputable def p29 : RealPoly := [v33,v33,v33,v33,v33,v33,v33,v33,v33,v33,v33,v675,v676,v677,v674,v671,v668,v665,v662,v659,v656,v653,v650,v647]
theorem p29_eq : p29=List.replicate 11 (0 : ℝ)++p20 := by
  norm_num [p29,p20,v33,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p30 : RealPoly := [v720,v720,v720,v720,v720,v720,v720,v720,v720,v720,v720,v721,v722,v723,v724,v725,v726,v727,v728,v729,v730,v731,v732,v733]
theorem p30_eq : p30=RealPoly.scale v719 p29 := by
  norm_num [p30,p29,v33,v720,v721,v722,v723,v724,v725,v726,v727,v728,v729,v730,v731,v732,v733,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p31 : RealPoly := [v734,v735,v736,v737,v738,v739,v740,v741,v742,v743,v744,v745,v746,v747,v748,v749,v750,v751,v752,v753,v754,v755,v756,v757]
theorem p31_eq : p31=RealPoly.add p28 p30 := by
  norm_num [p31,p28,p30,v734,v735,v736,v737,v738,v739,v740,v741,v742,v743,v744,v745,v746,v747,v748,v749,v750,v751,v752,v753,v754,v755,v756,v757,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p32 : RealPoly := [v33,v33,v33,v33,v33,v33,v33,v33,v33,v33,v33,v717]
noncomputable def p33 : RealPoly := [v758,v718,v718,v718,v718,v718,v718,v718,v718,v718,v718,v759,v449]
theorem p33_eq : p33=RealPoly.add p27 p32 := by
  norm_num [p33,p27,p32,v33,v758,v759,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p34 : RealPoly := [v734,v735,v736,v737,v738,v739,v740,v741,v742,v743,v744,v745,v746,v747,v748,v749,v750,v751,v752,v753,v754,v755,v756]
noncomputable def p35 : RealPoly := [v33,v33,v33,v33,v33,v33,v33,v33,v33,v33,v675,v676,v677,v674,v671,v668,v665,v662,v659,v656,v653,v650,v647]
theorem p35_eq : p35=List.replicate 10 (0 : ℝ)++p20 := by
  norm_num [p35,p20,v33,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p36 : RealPoly := [v761,v761,v761,v761,v761,v761,v761,v761,v761,v761,v762,v763,v764,v765,v766,v767,v768,v769,v770,v771,v772,v773,v774]
theorem p36_eq : p36=RealPoly.scale v760 p35 := by
  norm_num [p36,p35,v33,v761,v762,v763,v764,v765,v766,v767,v768,v769,v770,v771,v772,v773,v774,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p37 : RealPoly := [v775,v776,v777,v778,v779,v780,v781,v782,v783,v784,v785,v786,v787,v788,v789,v790,v791,v792,v793,v794,v795,v796,v797]
theorem p37_eq : p37=RealPoly.add p34 p36 := by
  norm_num [p37,p34,p36,v775,v776,v777,v778,v779,v780,v781,v782,v783,v784,v785,v786,v787,v788,v789,v790,v791,v792,v793,v794,v795,v796,v797,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p38 : RealPoly := [v33,v33,v33,v33,v33,v33,v33,v33,v33,v33,v757]
noncomputable def p39 : RealPoly := [v798,v758,v758,v758,v758,v758,v758,v758,v758,v758,v799,v759,v449]
theorem p39_eq : p39=RealPoly.add p33 p38 := by
  norm_num [p39,p33,p38,v33,v798,v799,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p40 : RealPoly := [v775,v776,v777,v778,v779,v780,v781,v782,v783,v784,v785,v786,v787,v788,v789,v790,v791,v792,v793,v794,v795,v796]
noncomputable def p41 : RealPoly := [v33,v33,v33,v33,v33,v33,v33,v33,v33,v675,v676,v677,v674,v671,v668,v665,v662,v659,v656,v653,v650,v647]
theorem p41_eq : p41=List.replicate 9 (0 : ℝ)++p20 := by
  norm_num [p41,p20,v33,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p42 : RealPoly := [v801,v801,v801,v801,v801,v801,v801,v801,v801,v802,v803,v804,v805,v806,v807,v808,v809,v810,v811,v812,v813,v814]
theorem p42_eq : p42=RealPoly.scale v800 p41 := by
  norm_num [p42,p41,v33,v801,v802,v803,v804,v805,v806,v807,v808,v809,v810,v811,v812,v813,v814,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p43 : RealPoly := [v815,v816,v817,v818,v819,v820,v821,v822,v823,v824,v825,v826,v827,v828,v829,v830,v831,v832,v833,v834,v835,v836]
theorem p43_eq : p43=RealPoly.add p40 p42 := by
  norm_num [p43,p40,p42,v815,v816,v817,v818,v819,v820,v821,v822,v823,v824,v825,v826,v827,v828,v829,v830,v831,v832,v833,v834,v835,v836,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p44 : RealPoly := [v33,v33,v33,v33,v33,v33,v33,v33,v33,v797]
noncomputable def p45 : RealPoly := [v837,v798,v798,v798,v798,v798,v798,v798,v798,v838,v799,v759,v449]
theorem p45_eq : p45=RealPoly.add p39 p44 := by
  norm_num [p45,p39,p44,v33,v837,v838,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p46 : RealPoly := [v815,v816,v817,v818,v819,v820,v821,v822,v823,v824,v825,v826,v827,v828,v829,v830,v831,v832,v833,v834,v835]
noncomputable def p47 : RealPoly := [v33,v33,v33,v33,v33,v33,v33,v33,v675,v676,v677,v674,v671,v668,v665,v662,v659,v656,v653,v650,v647]
theorem p47_eq : p47=List.replicate 8 (0 : ℝ)++p20 := by
  norm_num [p47,p20,v33,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p48 : RealPoly := [v840,v840,v840,v840,v840,v840,v840,v840,v841,v842,v843,v844,v845,v846,v847,v848,v849,v850,v851,v852,v853]
theorem p48_eq : p48=RealPoly.scale v839 p47 := by
  norm_num [p48,p47,v33,v840,v841,v842,v843,v844,v845,v846,v847,v848,v849,v850,v851,v852,v853,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p49 : RealPoly := [v854,v855,v856,v857,v858,v859,v860,v861,v862,v863,v864,v865,v866,v867,v868,v869,v870,v871,v872,v873,v874]
theorem p49_eq : p49=RealPoly.add p46 p48 := by
  norm_num [p49,p46,p48,v854,v855,v856,v857,v858,v859,v860,v861,v862,v863,v864,v865,v866,v867,v868,v869,v870,v871,v872,v873,v874,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p50 : RealPoly := [v33,v33,v33,v33,v33,v33,v33,v33,v836]
noncomputable def p51 : RealPoly := [v875,v837,v837,v837,v837,v837,v837,v837,v876,v838,v799,v759,v449]
theorem p51_eq : p51=RealPoly.add p45 p50 := by
  norm_num [p51,p45,p50,v33,v875,v876,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p52 : RealPoly := [v854,v855,v856,v857,v858,v859,v860,v861,v862,v863,v864,v865,v866,v867,v868,v869,v870,v871,v872,v873]
noncomputable def p53 : RealPoly := [v33,v33,v33,v33,v33,v33,v33,v675,v676,v677,v674,v671,v668,v665,v662,v659,v656,v653,v650,v647]
theorem p53_eq : p53=List.replicate 7 (0 : ℝ)++p20 := by
  norm_num [p53,p20,v33,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p54 : RealPoly := [v878,v878,v878,v878,v878,v878,v878,v879,v880,v881,v882,v883,v884,v885,v886,v887,v888,v889,v890,v891]
theorem p54_eq : p54=RealPoly.scale v877 p53 := by
  norm_num [p54,p53,v33,v878,v879,v880,v881,v882,v883,v884,v885,v886,v887,v888,v889,v890,v891,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p55 : RealPoly := [v892,v893,v894,v895,v896,v897,v898,v899,v900,v901,v902,v903,v904,v905,v906,v907,v908,v909,v910,v911]
theorem p55_eq : p55=RealPoly.add p52 p54 := by
  norm_num [p55,p52,p54,v892,v893,v894,v895,v896,v897,v898,v899,v900,v901,v902,v903,v904,v905,v906,v907,v908,v909,v910,v911,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p56 : RealPoly := [v33,v33,v33,v33,v33,v33,v33,v874]
noncomputable def p57 : RealPoly := [v912,v875,v875,v875,v875,v875,v875,v913,v876,v838,v799,v759,v449]
theorem p57_eq : p57=RealPoly.add p51 p56 := by
  norm_num [p57,p51,p56,v33,v912,v913,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p58 : RealPoly := [v892,v893,v894,v895,v896,v897,v898,v899,v900,v901,v902,v903,v904,v905,v906,v907,v908,v909,v910]
noncomputable def p59 : RealPoly := [v33,v33,v33,v33,v33,v33,v675,v676,v677,v674,v671,v668,v665,v662,v659,v656,v653,v650,v647]
theorem p59_eq : p59=List.replicate 6 (0 : ℝ)++p20 := by
  norm_num [p59,p20,v33,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p60 : RealPoly := [v915,v915,v915,v915,v915,v915,v916,v917,v918,v919,v920,v921,v922,v923,v924,v925,v926,v927,v928]
theorem p60_eq : p60=RealPoly.scale v914 p59 := by
  norm_num [p60,p59,v33,v915,v916,v917,v918,v919,v920,v921,v922,v923,v924,v925,v926,v927,v928,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p61 : RealPoly := [v929,v930,v931,v932,v933,v934,v935,v936,v937,v938,v939,v940,v941,v942,v943,v944,v945,v946,v947]
theorem p61_eq : p61=RealPoly.add p58 p60 := by
  norm_num [p61,p58,p60,v929,v930,v931,v932,v933,v934,v935,v936,v937,v938,v939,v940,v941,v942,v943,v944,v945,v946,v947,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p62 : RealPoly := [v33,v33,v33,v33,v33,v33,v911]
noncomputable def p63 : RealPoly := [v948,v912,v912,v912,v912,v912,v949,v913,v876,v838,v799,v759,v449]
theorem p63_eq : p63=RealPoly.add p57 p62 := by
  norm_num [p63,p57,p62,v33,v948,v949,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p64 : RealPoly := [v929,v930,v931,v932,v933,v934,v935,v936,v937,v938,v939,v940,v941,v942,v943,v944,v945,v946]
noncomputable def p65 : RealPoly := [v33,v33,v33,v33,v33,v675,v676,v677,v674,v671,v668,v665,v662,v659,v656,v653,v650,v647]
theorem p65_eq : p65=List.replicate 5 (0 : ℝ)++p20 := by
  norm_num [p65,p20,v33,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p66 : RealPoly := [v951,v951,v951,v951,v951,v952,v953,v954,v955,v956,v957,v958,v959,v960,v961,v962,v963,v964]
theorem p66_eq : p66=RealPoly.scale v950 p65 := by
  norm_num [p66,p65,v33,v951,v952,v953,v954,v955,v956,v957,v958,v959,v960,v961,v962,v963,v964,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p67 : RealPoly := [v965,v966,v967,v968,v969,v970,v971,v972,v973,v974,v975,v976,v977,v978,v979,v980,v981,v982]
theorem p67_eq : p67=RealPoly.add p64 p66 := by
  norm_num [p67,p64,p66,v965,v966,v967,v968,v969,v970,v971,v972,v973,v974,v975,v976,v977,v978,v979,v980,v981,v982,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p68 : RealPoly := [v33,v33,v33,v33,v33,v947]
noncomputable def p69 : RealPoly := [v983,v948,v948,v948,v948,v984,v949,v913,v876,v838,v799,v759,v449]
theorem p69_eq : p69=RealPoly.add p63 p68 := by
  norm_num [p69,p63,p68,v33,v983,v984,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p70 : RealPoly := [v965,v966,v967,v968,v969,v970,v971,v972,v973,v974,v975,v976,v977,v978,v979,v980,v981]
noncomputable def p71 : RealPoly := [v33,v33,v33,v33,v675,v676,v677,v674,v671,v668,v665,v662,v659,v656,v653,v650,v647]
theorem p71_eq : p71=List.replicate 4 (0 : ℝ)++p20 := by
  norm_num [p71,p20,v33,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p72 : RealPoly := [v986,v986,v986,v986,v987,v988,v989,v990,v991,v992,v993,v994,v995,v996,v997,v998,v999]
theorem p72_eq : p72=RealPoly.scale v985 p71 := by
  norm_num [p72,p71,v33,v986,v987,v988,v989,v990,v991,v992,v993,v994,v995,v996,v997,v998,v999,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p73 : RealPoly := [v1000,v1001,v1002,v1003,v1004,v1005,v1006,v1007,v1008,v1009,v1010,v1011,v1012,v1013,v1014,v1015,v1016]
theorem p73_eq : p73=RealPoly.add p70 p72 := by
  norm_num [p73,p70,p72,v1000,v1001,v1002,v1003,v1004,v1005,v1006,v1007,v1008,v1009,v1010,v1011,v1012,v1013,v1014,v1015,v1016,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p74 : RealPoly := [v33,v33,v33,v33,v982]
noncomputable def p75 : RealPoly := [v1017,v983,v983,v983,v1018,v984,v949,v913,v876,v838,v799,v759,v449]
theorem p75_eq : p75=RealPoly.add p69 p74 := by
  norm_num [p75,p69,p74,v33,v1017,v1018,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p76 : RealPoly := [v1000,v1001,v1002,v1003,v1004,v1005,v1006,v1007,v1008,v1009,v1010,v1011,v1012,v1013,v1014,v1015]
noncomputable def p77 : RealPoly := [v33,v33,v33,v675,v676,v677,v674,v671,v668,v665,v662,v659,v656,v653,v650,v647]
theorem p77_eq : p77=List.replicate 3 (0 : ℝ)++p20 := by
  norm_num [p77,p20,v33,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p78 : RealPoly := [v1020,v1020,v1020,v1021,v1022,v1023,v1024,v1025,v1026,v1027,v1028,v1029,v1030,v1031,v1032,v1033]
theorem p78_eq : p78=RealPoly.scale v1019 p77 := by
  norm_num [p78,p77,v33,v1020,v1021,v1022,v1023,v1024,v1025,v1026,v1027,v1028,v1029,v1030,v1031,v1032,v1033,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p79 : RealPoly := [v1034,v1035,v1036,v1037,v1038,v1039,v1040,v1041,v1042,v1043,v1044,v1045,v1046,v1047,v1048,v1049]
theorem p79_eq : p79=RealPoly.add p76 p78 := by
  norm_num [p79,p76,p78,v1034,v1035,v1036,v1037,v1038,v1039,v1040,v1041,v1042,v1043,v1044,v1045,v1046,v1047,v1048,v1049,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p80 : RealPoly := [v33,v33,v33,v1016]
noncomputable def p81 : RealPoly := [v1050,v1017,v1017,v1051,v1018,v984,v949,v913,v876,v838,v799,v759,v449]
theorem p81_eq : p81=RealPoly.add p75 p80 := by
  norm_num [p81,p75,p80,v33,v1050,v1051,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p82 : RealPoly := [v1034,v1035,v1036,v1037,v1038,v1039,v1040,v1041,v1042,v1043,v1044,v1045,v1046,v1047,v1048]
noncomputable def p83 : RealPoly := [v33,v33,v675,v676,v677,v674,v671,v668,v665,v662,v659,v656,v653,v650,v647]
theorem p83_eq : p83=List.replicate 2 (0 : ℝ)++p20 := by
  norm_num [p83,p20,v33,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p84 : RealPoly := [v1053,v1053,v1054,v1055,v1056,v1057,v1058,v1059,v1060,v1061,v1062,v1063,v1064,v1065,v1066]
theorem p84_eq : p84=RealPoly.scale v1052 p83 := by
  norm_num [p84,p83,v33,v1053,v1054,v1055,v1056,v1057,v1058,v1059,v1060,v1061,v1062,v1063,v1064,v1065,v1066,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p85 : RealPoly := [v1067,v1068,v1069,v1070,v1071,v1072,v1073,v1074,v1075,v1076,v1077,v1078,v1079,v1080,v1081]
theorem p85_eq : p85=RealPoly.add p82 p84 := by
  norm_num [p85,p82,p84,v1067,v1068,v1069,v1070,v1071,v1072,v1073,v1074,v1075,v1076,v1077,v1078,v1079,v1080,v1081,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p86 : RealPoly := [v33,v33,v1049]
noncomputable def p87 : RealPoly := [v1082,v1050,v1083,v1051,v1018,v984,v949,v913,v876,v838,v799,v759,v449]
theorem p87_eq : p87=RealPoly.add p81 p86 := by
  norm_num [p87,p81,p86,v33,v1082,v1083,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p88 : RealPoly := [v1067,v1068,v1069,v1070,v1071,v1072,v1073,v1074,v1075,v1076,v1077,v1078,v1079,v1080]
noncomputable def p89 : RealPoly := [v33,v675,v676,v677,v674,v671,v668,v665,v662,v659,v656,v653,v650,v647]
theorem p89_eq : p89=List.replicate 1 (0 : ℝ)++p20 := by
  norm_num [p89,p20,v33,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p90 : RealPoly := [v1085,v1086,v1087,v1088,v1089,v1090,v1091,v1092,v1093,v1094,v1095,v1096,v1097,v1098]
theorem p90_eq : p90=RealPoly.scale v1084 p89 := by
  norm_num [p90,p89,v33,v1085,v1086,v1087,v1088,v1089,v1090,v1091,v1092,v1093,v1094,v1095,v1096,v1097,v1098,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p91 : RealPoly := [v1099,v1100,v1101,v1102,v1103,v1104,v1105,v1106,v1107,v1108,v1109,v1110,v1111,v1112]
theorem p91_eq : p91=RealPoly.add p88 p90 := by
  norm_num [p91,p88,p90,v1099,v1100,v1101,v1102,v1103,v1104,v1105,v1106,v1107,v1108,v1109,v1110,v1111,v1112,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p92 : RealPoly := [v33,v1081]
noncomputable def p93 : RealPoly := [v1113,v1114,v1083,v1051,v1018,v984,v949,v913,v876,v838,v799,v759,v449]
theorem p93_eq : p93=RealPoly.add p87 p92 := by
  norm_num [p93,p87,p92,v33,v1113,v1114,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p94 : RealPoly := [v1099,v1100,v1101,v1102,v1103,v1104,v1105,v1106,v1107,v1108,v1109,v1110,v1111]
noncomputable def p95 : RealPoly := [v675,v676,v677,v674,v671,v668,v665,v662,v659,v656,v653,v650,v647]
theorem p95_eq : p95=List.replicate 0 (0 : ℝ)++p20 := by
  norm_num [p95,p20,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p96 : RealPoly := [v1116,v1117,v1118,v1119,v1120,v1121,v1122,v1123,v1124,v1125,v1126,v1127,v1128]
theorem p96_eq : p96=RealPoly.scale v1115 p95 := by
  norm_num [p96,p95,v1116,v1117,v1118,v1119,v1120,v1121,v1122,v1123,v1124,v1125,v1126,v1127,v1128,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p97 : RealPoly := [v1129,v1130,v1131,v1132,v1133,v1134,v1135,v1136,v1137,v1138,v1139,v1140,v1141]
theorem p97_eq : p97=RealPoly.add p94 p96 := by
  norm_num [p97,p94,p96,v1129,v1130,v1131,v1132,v1133,v1134,v1135,v1136,v1137,v1138,v1139,v1140,v1141,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
noncomputable def p98 : RealPoly := [v1112]
noncomputable def p99 : RealPoly := [v1142,v1114,v1083,v1051,v1018,v984,v949,v913,v876,v838,v799,v759,v449]
theorem p99_eq : p99=RealPoly.add p93 p98 := by
  norm_num [p99,p93,p98,v1142,RealPoly.add,RealPoly.mul,RealPoly.scale,RealPoly.derivative,RealPoly.derivFrom,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  all_goals simp [mul_comm]
theorem hermite_model : p0.toPolynomial=Hpoly := HermiteArithmetic.hermite_model
theorem gap_model : p6.toPolynomial=squaredGap := by
  simp only [p3_eq,p4_eq,p5_eq,p6_eq,RealPoly.toPolynomial_add,RealPoly.toPolynomial_mul,RealPoly.toPolynomial_scale,hermite_model]
  norm_num [p1,p2,p3,p4,p5,p6,v17,v18,v19,v33,v423,v451,v452,v1169,v1172,v1175,v1178,v1181,v1186,v1189,v1192,v1195,v1198,v1205,v1208,v1211,v1214,v1217,v1233,v1236,v1239,v1242,v1246,v1249,v1252,v1266,v1269,v1287,v1292,v1295,v1299,v1320,RealPoly.toPolynomial,squaredGap]
  <;> ring <;> rfl

theorem power_model : p7.toPolynomial=(X+1)^5 := by
  apply Polynomial.funext
  intro x
  norm_num [p7,RealPoly.toPolynomial,v17,v451,v452,v452,v451,v17] <;> ring

theorem square_model0 : p9.toPolynomial=(X-C (nodes a 0))^2 := by
  rw [p9_eq,RealPoly.toPolynomial_mul]
  norm_num [p8,RealPoly.toPolynomial,v13,v17,v453]
  <;> ring

theorem square_model1 : p12.toPolynomial=(X-C (nodes a 1))^2 := by
  rw [p12_eq,RealPoly.toPolynomial_mul]
  norm_num [p11,RealPoly.toPolynomial,v14,v17,v483]
  <;> ring

theorem square_model2 : p15.toPolynomial=(X-C (nodes a 2))^2 := by
  rw [p15_eq,RealPoly.toPolynomial_mul]
  norm_num [p14,RealPoly.toPolynomial,v15,v17,v536]
  <;> ring

theorem square_model3 : p18.toPolynomial=(X-C (nodes a 3))^2 := by
  rw [p18_eq,RealPoly.toPolynomial_mul]
  norm_num [p17,RealPoly.toPolynomial,v16,v17,v601]
  <;> ring

theorem factor_model : p19.toPolynomial=contactFactor := by
  simp only [p10_eq,p13_eq,p16_eq,p19_eq,RealPoly.toPolynomial_mul,power_model,square_model0,square_model1,square_model2,square_model3]
  unfold contactFactor
  simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one]
  change _ = (X+1)^5*((X-C (nodes a 0))^2*((X-C (nodes a 1))^2*((X-C (nodes a 2))^2*(X-C (nodes a 3))^2)))
  ring

theorem leading_one : v643=1 := by
  have h := h643
  norm_num [Thomson8.Box.Contains,b643] at h
  linarith

theorem divisor_model : (p20++[1]).toPolynomial=contactFactor := by
  rw [←factor_model]
  simp only [p20,p19,leading_one,List.cons_append,List.nil_append]

theorem division_start : p6.toPolynomial=contactFactor*p21.toPolynomial+p6.toPolynomial := by
  norm_num [p21,RealPoly.toPolynomial,v33]

theorem term_monomial12 : p26.toPolynomial=C v449*X^12 := by
  apply Polynomial.funext
  intro x
  norm_num [p26,RealPoly.toPolynomial,v33] <;> ring

theorem division_step12 : p6.toPolynomial=contactFactor*p26.toPolynomial+p25.toPolynomial := by
  have hs := RealPoly.monic_step p22 p20 v449 12 (by rfl)
  rw [divisor_model] at hs
  rw [term_monomial12,p25_eq,p24_eq,p23_eq]
  simpa only [p22,p6,v678,List.cons_append,List.nil_append] using hs

theorem division_accum12 : p6.toPolynomial=contactFactor*p27.toPolynomial+p25.toPolynomial := by
  rw [division_start,division_step12,p27_eq,RealPoly.toPolynomial_add]
  ring

theorem term_monomial11 : p32.toPolynomial=C v717*X^11 := by
  apply Polynomial.funext
  intro x
  norm_num [p32,RealPoly.toPolynomial,v33] <;> ring

theorem division_step11 : p25.toPolynomial=contactFactor*p32.toPolynomial+p31.toPolynomial := by
  have hs := RealPoly.monic_step p28 p20 v717 11 (by rfl)
  rw [divisor_model] at hs
  rw [term_monomial11,p31_eq,p30_eq,p29_eq]
  simpa only [p28,p25,v719,List.cons_append,List.nil_append] using hs

theorem division_accum11 : p6.toPolynomial=contactFactor*p33.toPolynomial+p31.toPolynomial := by
  rw [division_accum12,division_step11,p33_eq,RealPoly.toPolynomial_add]
  ring

theorem term_monomial10 : p38.toPolynomial=C v757*X^10 := by
  apply Polynomial.funext
  intro x
  norm_num [p38,RealPoly.toPolynomial,v33] <;> ring

theorem division_step10 : p31.toPolynomial=contactFactor*p38.toPolynomial+p37.toPolynomial := by
  have hs := RealPoly.monic_step p34 p20 v757 10 (by rfl)
  rw [divisor_model] at hs
  rw [term_monomial10,p37_eq,p36_eq,p35_eq]
  simpa only [p34,p31,v760,List.cons_append,List.nil_append] using hs

theorem division_accum10 : p6.toPolynomial=contactFactor*p39.toPolynomial+p37.toPolynomial := by
  rw [division_accum11,division_step10,p39_eq,RealPoly.toPolynomial_add]
  ring

theorem term_monomial9 : p44.toPolynomial=C v797*X^9 := by
  apply Polynomial.funext
  intro x
  norm_num [p44,RealPoly.toPolynomial,v33] <;> ring

theorem division_step9 : p37.toPolynomial=contactFactor*p44.toPolynomial+p43.toPolynomial := by
  have hs := RealPoly.monic_step p40 p20 v797 9 (by rfl)
  rw [divisor_model] at hs
  rw [term_monomial9,p43_eq,p42_eq,p41_eq]
  simpa only [p40,p37,v800,List.cons_append,List.nil_append] using hs

theorem division_accum9 : p6.toPolynomial=contactFactor*p45.toPolynomial+p43.toPolynomial := by
  rw [division_accum10,division_step9,p45_eq,RealPoly.toPolynomial_add]
  ring

theorem term_monomial8 : p50.toPolynomial=C v836*X^8 := by
  apply Polynomial.funext
  intro x
  norm_num [p50,RealPoly.toPolynomial,v33] <;> ring

theorem division_step8 : p43.toPolynomial=contactFactor*p50.toPolynomial+p49.toPolynomial := by
  have hs := RealPoly.monic_step p46 p20 v836 8 (by rfl)
  rw [divisor_model] at hs
  rw [term_monomial8,p49_eq,p48_eq,p47_eq]
  simpa only [p46,p43,v839,List.cons_append,List.nil_append] using hs

theorem division_accum8 : p6.toPolynomial=contactFactor*p51.toPolynomial+p49.toPolynomial := by
  rw [division_accum9,division_step8,p51_eq,RealPoly.toPolynomial_add]
  ring

theorem term_monomial7 : p56.toPolynomial=C v874*X^7 := by
  apply Polynomial.funext
  intro x
  norm_num [p56,RealPoly.toPolynomial,v33] <;> ring

theorem division_step7 : p49.toPolynomial=contactFactor*p56.toPolynomial+p55.toPolynomial := by
  have hs := RealPoly.monic_step p52 p20 v874 7 (by rfl)
  rw [divisor_model] at hs
  rw [term_monomial7,p55_eq,p54_eq,p53_eq]
  simpa only [p52,p49,v877,List.cons_append,List.nil_append] using hs

theorem division_accum7 : p6.toPolynomial=contactFactor*p57.toPolynomial+p55.toPolynomial := by
  rw [division_accum8,division_step7,p57_eq,RealPoly.toPolynomial_add]
  ring

theorem term_monomial6 : p62.toPolynomial=C v911*X^6 := by
  apply Polynomial.funext
  intro x
  norm_num [p62,RealPoly.toPolynomial,v33] <;> ring

theorem division_step6 : p55.toPolynomial=contactFactor*p62.toPolynomial+p61.toPolynomial := by
  have hs := RealPoly.monic_step p58 p20 v911 6 (by rfl)
  rw [divisor_model] at hs
  rw [term_monomial6,p61_eq,p60_eq,p59_eq]
  simpa only [p58,p55,v914,List.cons_append,List.nil_append] using hs

theorem division_accum6 : p6.toPolynomial=contactFactor*p63.toPolynomial+p61.toPolynomial := by
  rw [division_accum7,division_step6,p63_eq,RealPoly.toPolynomial_add]
  ring

theorem term_monomial5 : p68.toPolynomial=C v947*X^5 := by
  apply Polynomial.funext
  intro x
  norm_num [p68,RealPoly.toPolynomial,v33] <;> ring

theorem division_step5 : p61.toPolynomial=contactFactor*p68.toPolynomial+p67.toPolynomial := by
  have hs := RealPoly.monic_step p64 p20 v947 5 (by rfl)
  rw [divisor_model] at hs
  rw [term_monomial5,p67_eq,p66_eq,p65_eq]
  simpa only [p64,p61,v950,List.cons_append,List.nil_append] using hs

theorem division_accum5 : p6.toPolynomial=contactFactor*p69.toPolynomial+p67.toPolynomial := by
  rw [division_accum6,division_step5,p69_eq,RealPoly.toPolynomial_add]
  ring

theorem term_monomial4 : p74.toPolynomial=C v982*X^4 := by
  apply Polynomial.funext
  intro x
  norm_num [p74,RealPoly.toPolynomial,v33] <;> ring

theorem division_step4 : p67.toPolynomial=contactFactor*p74.toPolynomial+p73.toPolynomial := by
  have hs := RealPoly.monic_step p70 p20 v982 4 (by rfl)
  rw [divisor_model] at hs
  rw [term_monomial4,p73_eq,p72_eq,p71_eq]
  simpa only [p70,p67,v985,List.cons_append,List.nil_append] using hs

theorem division_accum4 : p6.toPolynomial=contactFactor*p75.toPolynomial+p73.toPolynomial := by
  rw [division_accum5,division_step4,p75_eq,RealPoly.toPolynomial_add]
  ring

theorem term_monomial3 : p80.toPolynomial=C v1016*X^3 := by
  apply Polynomial.funext
  intro x
  norm_num [p80,RealPoly.toPolynomial,v33] <;> ring

theorem division_step3 : p73.toPolynomial=contactFactor*p80.toPolynomial+p79.toPolynomial := by
  have hs := RealPoly.monic_step p76 p20 v1016 3 (by rfl)
  rw [divisor_model] at hs
  rw [term_monomial3,p79_eq,p78_eq,p77_eq]
  simpa only [p76,p73,v1019,List.cons_append,List.nil_append] using hs

theorem division_accum3 : p6.toPolynomial=contactFactor*p81.toPolynomial+p79.toPolynomial := by
  rw [division_accum4,division_step3,p81_eq,RealPoly.toPolynomial_add]
  ring

theorem term_monomial2 : p86.toPolynomial=C v1049*X^2 := by
  apply Polynomial.funext
  intro x
  norm_num [p86,RealPoly.toPolynomial,v33] <;> ring

theorem division_step2 : p79.toPolynomial=contactFactor*p86.toPolynomial+p85.toPolynomial := by
  have hs := RealPoly.monic_step p82 p20 v1049 2 (by rfl)
  rw [divisor_model] at hs
  rw [term_monomial2,p85_eq,p84_eq,p83_eq]
  simpa only [p82,p79,v1052,List.cons_append,List.nil_append] using hs

theorem division_accum2 : p6.toPolynomial=contactFactor*p87.toPolynomial+p85.toPolynomial := by
  rw [division_accum3,division_step2,p87_eq,RealPoly.toPolynomial_add]
  ring

theorem term_monomial1 : p92.toPolynomial=C v1081*X^1 := by
  apply Polynomial.funext
  intro x
  norm_num [p92,RealPoly.toPolynomial,v33] <;> ring

theorem division_step1 : p85.toPolynomial=contactFactor*p92.toPolynomial+p91.toPolynomial := by
  have hs := RealPoly.monic_step p88 p20 v1081 1 (by rfl)
  rw [divisor_model] at hs
  rw [term_monomial1,p91_eq,p90_eq,p89_eq]
  simpa only [p88,p85,v1084,List.cons_append,List.nil_append] using hs

theorem division_accum1 : p6.toPolynomial=contactFactor*p93.toPolynomial+p91.toPolynomial := by
  rw [division_accum2,division_step1,p93_eq,RealPoly.toPolynomial_add]
  ring

theorem term_monomial0 : p98.toPolynomial=C v1112*X^0 := by
  apply Polynomial.funext
  intro x
  norm_num [p98,RealPoly.toPolynomial,v33] <;> ring

theorem division_step0 : p91.toPolynomial=contactFactor*p98.toPolynomial+p97.toPolynomial := by
  have hs := RealPoly.monic_step p94 p20 v1112 0 (by rfl)
  rw [divisor_model] at hs
  rw [term_monomial0,p97_eq,p96_eq,p95_eq]
  simpa only [p94,p91,v1115,List.cons_append,List.nil_append] using hs

theorem division_accum0 : p6.toPolynomial=contactFactor*p99.toPolynomial+p97.toPolynomial := by
  rw [division_accum1,division_step0,p99_eq,RealPoly.toPolynomial_add]
  ring

theorem remainder_zero : p97.toPolynomial=0 := by
  have hd : contactFactor ∣ p97.toPolynomial := by
    have he : p97.toPolynomial=squaredGap-contactFactor*p99.toPolynomial := by
      rw [←gap_model,division_accum0]
      ring
    rw [he]
    exact dvd_sub contactFactor_divides (dvd_mul_right _ _)
  apply eq_zero_of_dvd_of_natDegree_lt hd
  rw [contactFactor_degree]
  exact RealPoly.degree_lt_length (p := p97) (by intro h; cases h)

theorem quotient_model : p99.toPolynomial=gapQuotient := by
  apply mul_left_cancel₀ contactFactor_monic.ne_zero
  have hh := division_accum0
  rw [gap_model,remainder_zero,add_zero,squared_factorization] at hh
  exact hh.symm

end QuotientArithmetic
end Coulomb8

#print axioms Coulomb8.QuotientArithmetic.quotient_model
