import Coulomb8.QuotientModel
import Coulomb8.BernsteinSemantics

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

namespace Coulomb8
namespace QuotientArithmetic
open Polynomial
open Thomson8

theorem bernstein_formula0 (p : Polynomial ℝ) : bernsteinCoefficients p 0=((1 : ℚ) : ℝ)*p.coeff 0+(((-1 : ℚ) : ℝ)*p.coeff 1+(((1 : ℚ) : ℝ)*p.coeff 2+(((-1 : ℚ) : ℝ)*p.coeff 3+(((1 : ℚ) : ℝ)*p.coeff 4+(((-1 : ℚ) : ℝ)*p.coeff 5+(((1 : ℚ) : ℝ)*p.coeff 6+(((-1 : ℚ) : ℝ)*p.coeff 7+(((1 : ℚ) : ℝ)*p.coeff 8+(((-1 : ℚ) : ℝ)*p.coeff 9+(((1 : ℚ) : ℝ)*p.coeff 10+(((-1 : ℚ) : ℝ)*p.coeff 11+(((1 : ℚ) : ℝ)*p.coeff 12+(0))))))))))))) := by
  simp only [bernsteinCoefficients,Fin.sum_univ_succ]
  rfl

theorem bernstein_model0 : bernsteinCoefficients gapQuotient 0=v1168 := by
  rw [bernstein_formula0,←quotient_model]
  norm_num [RealPoly.coeff_toPolynomial,p99,v17,v33,v423,v1143,v1144,v1145,v1146,v1147,v1148,v1149,v1150,v1151,v1152,v1153,v1154,v1155,v1156,v1157,v1158,v1159,v1160,v1161,v1162,v1163,v1164,v1165,v1166,v1167,v1168] <;> ring_nf <;> rfl

theorem positive0 : 0 < bernsteinCoefficients gapQuotient 0 := by
  rw [bernstein_model0]
  exact Box.positive_of_contains h1168 (by decide +kernel)

theorem bernstein_formula1 (p : Polynomial ℝ) : bernsteinCoefficients p 1=((1 : ℚ) : ℝ)*p.coeff 0+((((-5/6) : ℚ) : ℝ)*p.coeff 1+((((2/3) : ℚ) : ℝ)*p.coeff 2+((((-1/2) : ℚ) : ℝ)*p.coeff 3+((((1/3) : ℚ) : ℝ)*p.coeff 4+((((-1/6) : ℚ) : ℝ)*p.coeff 5+(((0 : ℚ) : ℝ)*p.coeff 6+((((1/6) : ℚ) : ℝ)*p.coeff 7+((((-1/3) : ℚ) : ℝ)*p.coeff 8+((((1/2) : ℚ) : ℝ)*p.coeff 9+((((-2/3) : ℚ) : ℝ)*p.coeff 10+((((5/6) : ℚ) : ℝ)*p.coeff 11+(((-1 : ℚ) : ℝ)*p.coeff 12+(0))))))))))))) := by
  simp only [bernsteinCoefficients,Fin.sum_univ_succ]
  rfl

theorem bernstein_model1 : bernsteinCoefficients gapQuotient 1=v1202 := by
  rw [bernstein_formula1,←quotient_model]
  norm_num [RealPoly.coeff_toPolynomial,p99,v17,v33,v423,v1143,v1144,v1169,v1170,v1171,v1172,v1173,v1174,v1175,v1176,v1177,v1178,v1179,v1180,v1181,v1182,v1183,v1184,v1185,v1186,v1187,v1188,v1189,v1190,v1191,v1192,v1193,v1194,v1195,v1196,v1197,v1198,v1199,v1200,v1201,v1202] <;> ring_nf <;> rfl

theorem positive1 : 0 < bernsteinCoefficients gapQuotient 1 := by
  rw [bernstein_model1]
  exact Box.positive_of_contains h1202 (by decide +kernel)

theorem bernstein_formula2 (p : Polynomial ℝ) : bernsteinCoefficients p 2=((1 : ℚ) : ℝ)*p.coeff 0+((((-2/3) : ℚ) : ℝ)*p.coeff 1+((((13/33) : ℚ) : ℝ)*p.coeff 2+((((-2/11) : ℚ) : ℝ)*p.coeff 3+((((1/33) : ℚ) : ℝ)*p.coeff 4+((((2/33) : ℚ) : ℝ)*p.coeff 5+((((-1/11) : ℚ) : ℝ)*p.coeff 6+((((2/33) : ℚ) : ℝ)*p.coeff 7+((((1/33) : ℚ) : ℝ)*p.coeff 8+((((-2/11) : ℚ) : ℝ)*p.coeff 9+((((13/33) : ℚ) : ℝ)*p.coeff 10+((((-2/3) : ℚ) : ℝ)*p.coeff 11+(((1 : ℚ) : ℝ)*p.coeff 12+(0))))))))))))) := by
  simp only [bernsteinCoefficients,Fin.sum_univ_succ]
  rfl

theorem bernstein_model2 : bernsteinCoefficients gapQuotient 2=v1230 := by
  rw [bernstein_formula2,←quotient_model]
  norm_num [RealPoly.coeff_toPolynomial,p99,v17,v33,v1143,v1144,v1167,v1195,v1203,v1204,v1205,v1206,v1207,v1208,v1209,v1210,v1211,v1212,v1213,v1214,v1215,v1216,v1217,v1218,v1219,v1220,v1221,v1222,v1223,v1224,v1225,v1226,v1227,v1228,v1229,v1230] <;> ring_nf <;> rfl

theorem positive2 : 0 < bernsteinCoefficients gapQuotient 2 := by
  rw [bernstein_model2]
  exact Box.positive_of_contains h1230 (by decide +kernel)

theorem bernstein_formula3 (p : Polynomial ℝ) : bernsteinCoefficients p 3=((1 : ℚ) : ℝ)*p.coeff 0+((((-1/2) : ℚ) : ℝ)*p.coeff 1+((((2/11) : ℚ) : ℝ)*p.coeff 2+((((-1/110) : ℚ) : ℝ)*p.coeff 3+((((-3/55) : ℚ) : ℝ)*p.coeff 4+((((1/22) : ℚ) : ℝ)*p.coeff 5+(((0 : ℚ) : ℝ)*p.coeff 6+((((-1/22) : ℚ) : ℝ)*p.coeff 7+((((3/55) : ℚ) : ℝ)*p.coeff 8+((((1/110) : ℚ) : ℝ)*p.coeff 9+((((-2/11) : ℚ) : ℝ)*p.coeff 10+((((1/2) : ℚ) : ℝ)*p.coeff 11+(((-1 : ℚ) : ℝ)*p.coeff 12+(0))))))))))))) := by
  simp only [bernsteinCoefficients,Fin.sum_univ_succ]
  rfl

theorem bernstein_model3 : bernsteinCoefficients gapQuotient 3=v1259 := by
  rw [bernstein_formula3,←quotient_model]
  norm_num [RealPoly.coeff_toPolynomial,p99,v17,v33,v423,v1143,v1144,v1175,v1184,v1192,v1201,v1208,v1231,v1232,v1233,v1234,v1235,v1236,v1237,v1238,v1239,v1240,v1241,v1242,v1243,v1244,v1245,v1246,v1247,v1248,v1249,v1250,v1251,v1252,v1253,v1254,v1255,v1256,v1257,v1258,v1259] <;> ring_nf <;> rfl

theorem positive3 : 0 < bernsteinCoefficients gapQuotient 3 := by
  rw [bernstein_model3]
  exact Box.positive_of_contains h1259 (by decide +kernel)

theorem bernstein_formula4 (p : Polynomial ℝ) : bernsteinCoefficients p 4=((1 : ℚ) : ℝ)*p.coeff 0+((((-1/3) : ℚ) : ℝ)*p.coeff 1+((((1/33) : ℚ) : ℝ)*p.coeff 2+((((3/55) : ℚ) : ℝ)*p.coeff 3+((((-17/495) : ℚ) : ℝ)*p.coeff 4+((((-1/99) : ℚ) : ℝ)*p.coeff 5+((((1/33) : ℚ) : ℝ)*p.coeff 6+((((-1/99) : ℚ) : ℝ)*p.coeff 7+((((-17/495) : ℚ) : ℝ)*p.coeff 8+((((3/55) : ℚ) : ℝ)*p.coeff 9+((((1/33) : ℚ) : ℝ)*p.coeff 10+((((-1/3) : ℚ) : ℝ)*p.coeff 11+(((1 : ℚ) : ℝ)*p.coeff 12+(0))))))))))))) := by
  simp only [bernsteinCoefficients,Fin.sum_univ_succ]
  rfl

theorem bernstein_model4 : bernsteinCoefficients gapQuotient 4=v1284 := by
  rw [bernstein_formula4,←quotient_model]
  norm_num [RealPoly.coeff_toPolynomial,p99,v17,v33,v1143,v1144,v1167,v1189,v1211,v1249,v1260,v1261,v1262,v1263,v1264,v1265,v1266,v1267,v1268,v1269,v1270,v1271,v1272,v1273,v1274,v1275,v1276,v1277,v1278,v1279,v1280,v1281,v1282,v1283,v1284] <;> ring_nf <;> rfl

theorem positive4 : 0 < bernsteinCoefficients gapQuotient 4 := by
  rw [bernstein_model4]
  exact Box.positive_of_contains h1284 (by decide +kernel)

theorem bernstein_formula5 (p : Polynomial ℝ) : bernsteinCoefficients p 5=((1 : ℚ) : ℝ)*p.coeff 0+((((-1/6) : ℚ) : ℝ)*p.coeff 1+((((-2/33) : ℚ) : ℝ)*p.coeff 2+((((1/22) : ℚ) : ℝ)*p.coeff 3+((((1/99) : ℚ) : ℝ)*p.coeff 4+((((-5/198) : ℚ) : ℝ)*p.coeff 5+(((0 : ℚ) : ℝ)*p.coeff 6+((((5/198) : ℚ) : ℝ)*p.coeff 7+((((-1/99) : ℚ) : ℝ)*p.coeff 8+((((-1/22) : ℚ) : ℝ)*p.coeff 9+((((2/33) : ℚ) : ℝ)*p.coeff 10+((((1/6) : ℚ) : ℝ)*p.coeff 11+(((-1 : ℚ) : ℝ)*p.coeff 12+(0))))))))))))) := by
  simp only [bernsteinCoefficients,Fin.sum_univ_succ]
  rfl

theorem bernstein_model5 : bernsteinCoefficients gapQuotient 5=v1310 := by
  rw [bernstein_formula5,←quotient_model]
  norm_num [RealPoly.coeff_toPolynomial,p99,v17,v33,v423,v1143,v1144,v1181,v1184,v1186,v1201,v1214,v1242,v1246,v1269,v1285,v1286,v1287,v1288,v1289,v1290,v1291,v1292,v1293,v1294,v1295,v1296,v1297,v1298,v1299,v1300,v1301,v1302,v1303,v1304,v1305,v1306,v1307,v1308,v1309,v1310] <;> ring_nf <;> rfl

theorem positive5 : 0 < bernsteinCoefficients gapQuotient 5 := by
  rw [bernstein_model5]
  exact Box.positive_of_contains h1310 (by decide +kernel)

theorem bernstein_formula6 (p : Polynomial ℝ) : bernsteinCoefficients p 6=((1 : ℚ) : ℝ)*p.coeff 0+(((0 : ℚ) : ℝ)*p.coeff 1+((((-1/11) : ℚ) : ℝ)*p.coeff 2+(((0 : ℚ) : ℝ)*p.coeff 3+((((1/33) : ℚ) : ℝ)*p.coeff 4+(((0 : ℚ) : ℝ)*p.coeff 5+((((-5/231) : ℚ) : ℝ)*p.coeff 6+(((0 : ℚ) : ℝ)*p.coeff 7+((((1/33) : ℚ) : ℝ)*p.coeff 8+(((0 : ℚ) : ℝ)*p.coeff 9+((((-1/11) : ℚ) : ℝ)*p.coeff 10+(((0 : ℚ) : ℝ)*p.coeff 11+(((1 : ℚ) : ℝ)*p.coeff 12+(0))))))))))))) := by
  simp only [bernsteinCoefficients,Fin.sum_univ_succ]
  rfl

theorem bernstein_model6 : bernsteinCoefficients gapQuotient 6=v1332 := by
  rw [bernstein_formula6,←quotient_model]
  norm_num [RealPoly.coeff_toPolynomial,p99,v17,v33,v1143,v1144,v1167,v1211,v1212,v1217,v1222,v1311,v1312,v1313,v1314,v1315,v1316,v1317,v1318,v1319,v1320,v1321,v1322,v1323,v1324,v1325,v1326,v1327,v1328,v1329,v1330,v1331,v1332] <;> ring_nf <;> rfl

theorem positive6 : 0 < bernsteinCoefficients gapQuotient 6 := by
  rw [bernstein_model6]
  exact Box.positive_of_contains h1332 (by decide +kernel)

theorem bernstein_formula7 (p : Polynomial ℝ) : bernsteinCoefficients p 7=((1 : ℚ) : ℝ)*p.coeff 0+((((1/6) : ℚ) : ℝ)*p.coeff 1+((((-2/33) : ℚ) : ℝ)*p.coeff 2+((((-1/22) : ℚ) : ℝ)*p.coeff 3+((((1/99) : ℚ) : ℝ)*p.coeff 4+((((5/198) : ℚ) : ℝ)*p.coeff 5+(((0 : ℚ) : ℝ)*p.coeff 6+((((-5/198) : ℚ) : ℝ)*p.coeff 7+((((-1/99) : ℚ) : ℝ)*p.coeff 8+((((1/22) : ℚ) : ℝ)*p.coeff 9+((((2/33) : ℚ) : ℝ)*p.coeff 10+((((-1/6) : ℚ) : ℝ)*p.coeff 11+(((-1 : ℚ) : ℝ)*p.coeff 12+(0))))))))))))) := by
  simp only [bernsteinCoefficients,Fin.sum_univ_succ]
  rfl

theorem bernstein_model7 : bernsteinCoefficients gapQuotient 7=v1350 := by
  rw [bernstein_formula7,←quotient_model]
  norm_num [RealPoly.coeff_toPolynomial,p99,v17,v33,v423,v1143,v1144,v1181,v1184,v1186,v1201,v1214,v1242,v1246,v1269,v1287,v1288,v1292,v1293,v1295,v1299,v1302,v1306,v1333,v1334,v1335,v1336,v1337,v1338,v1339,v1340,v1341,v1342,v1343,v1344,v1345,v1346,v1347,v1348,v1349,v1350] <;> ring_nf <;> rfl

theorem positive7 : 0 < bernsteinCoefficients gapQuotient 7 := by
  rw [bernstein_model7]
  exact Box.positive_of_contains h1350 (by decide +kernel)

theorem bernstein_formula8 (p : Polynomial ℝ) : bernsteinCoefficients p 8=((1 : ℚ) : ℝ)*p.coeff 0+((((1/3) : ℚ) : ℝ)*p.coeff 1+((((1/33) : ℚ) : ℝ)*p.coeff 2+((((-3/55) : ℚ) : ℝ)*p.coeff 3+((((-17/495) : ℚ) : ℝ)*p.coeff 4+((((1/99) : ℚ) : ℝ)*p.coeff 5+((((1/33) : ℚ) : ℝ)*p.coeff 6+((((1/99) : ℚ) : ℝ)*p.coeff 7+((((-17/495) : ℚ) : ℝ)*p.coeff 8+((((-3/55) : ℚ) : ℝ)*p.coeff 9+((((1/33) : ℚ) : ℝ)*p.coeff 10+((((1/3) : ℚ) : ℝ)*p.coeff 11+(((1 : ℚ) : ℝ)*p.coeff 12+(0))))))))))))) := by
  simp only [bernsteinCoefficients,Fin.sum_univ_succ]
  rfl

theorem bernstein_model8 : bernsteinCoefficients gapQuotient 8=v1368 := by
  rw [bernstein_formula8,←quotient_model]
  norm_num [RealPoly.coeff_toPolynomial,p99,v17,v33,v1143,v1144,v1167,v1178,v1211,v1239,v1262,v1266,v1267,v1272,v1276,v1280,v1292,v1351,v1352,v1353,v1354,v1355,v1356,v1357,v1358,v1359,v1360,v1361,v1362,v1363,v1364,v1365,v1366,v1367,v1368] <;> ring_nf <;> rfl

theorem positive8 : 0 < bernsteinCoefficients gapQuotient 8 := by
  rw [bernstein_model8]
  exact Box.positive_of_contains h1368 (by decide +kernel)

theorem bernstein_formula9 (p : Polynomial ℝ) : bernsteinCoefficients p 9=((1 : ℚ) : ℝ)*p.coeff 0+((((1/2) : ℚ) : ℝ)*p.coeff 1+((((2/11) : ℚ) : ℝ)*p.coeff 2+((((1/110) : ℚ) : ℝ)*p.coeff 3+((((-3/55) : ℚ) : ℝ)*p.coeff 4+((((-1/22) : ℚ) : ℝ)*p.coeff 5+(((0 : ℚ) : ℝ)*p.coeff 6+((((1/22) : ℚ) : ℝ)*p.coeff 7+((((3/55) : ℚ) : ℝ)*p.coeff 8+((((-1/110) : ℚ) : ℝ)*p.coeff 9+((((-2/11) : ℚ) : ℝ)*p.coeff 10+((((-1/2) : ℚ) : ℝ)*p.coeff 11+(((-1 : ℚ) : ℝ)*p.coeff 12+(0))))))))))))) := by
  simp only [bernsteinCoefficients,Fin.sum_univ_succ]
  rfl

theorem bernstein_model9 : bernsteinCoefficients gapQuotient 9=v1386 := by
  rw [bernstein_formula9,←quotient_model]
  norm_num [RealPoly.coeff_toPolynomial,p99,v17,v33,v423,v1143,v1144,v1175,v1184,v1192,v1201,v1208,v1233,v1234,v1236,v1239,v1240,v1242,v1246,v1249,v1250,v1252,v1255,v1369,v1370,v1371,v1372,v1373,v1374,v1375,v1376,v1377,v1378,v1379,v1380,v1381,v1382,v1383,v1384,v1385,v1386] <;> ring_nf <;> rfl

theorem positive9 : 0 < bernsteinCoefficients gapQuotient 9 := by
  rw [bernstein_model9]
  exact Box.positive_of_contains h1386 (by decide +kernel)

theorem bernstein_formula10 (p : Polynomial ℝ) : bernsteinCoefficients p 10=((1 : ℚ) : ℝ)*p.coeff 0+((((2/3) : ℚ) : ℝ)*p.coeff 1+((((13/33) : ℚ) : ℝ)*p.coeff 2+((((2/11) : ℚ) : ℝ)*p.coeff 3+((((1/33) : ℚ) : ℝ)*p.coeff 4+((((-2/33) : ℚ) : ℝ)*p.coeff 5+((((-1/11) : ℚ) : ℝ)*p.coeff 6+((((-2/33) : ℚ) : ℝ)*p.coeff 7+((((1/33) : ℚ) : ℝ)*p.coeff 8+((((2/11) : ℚ) : ℝ)*p.coeff 9+((((13/33) : ℚ) : ℝ)*p.coeff 10+((((2/3) : ℚ) : ℝ)*p.coeff 11+(((1 : ℚ) : ℝ)*p.coeff 12+(0))))))))))))) := by
  simp only [bernsteinCoefficients,Fin.sum_univ_succ]
  rfl

theorem bernstein_model10 : bernsteinCoefficients gapQuotient 10=v1404 := by
  rw [bernstein_formula10,←quotient_model]
  norm_num [RealPoly.coeff_toPolynomial,p99,v17,v33,v1143,v1144,v1167,v1172,v1205,v1206,v1211,v1212,v1217,v1218,v1222,v1226,v1233,v1287,v1387,v1388,v1389,v1390,v1391,v1392,v1393,v1394,v1395,v1396,v1397,v1398,v1399,v1400,v1401,v1402,v1403,v1404] <;> ring_nf <;> rfl

theorem positive10 : 0 < bernsteinCoefficients gapQuotient 10 := by
  rw [bernstein_model10]
  exact Box.positive_of_contains h1404 (by decide +kernel)

theorem bernstein_formula11 (p : Polynomial ℝ) : bernsteinCoefficients p 11=((1 : ℚ) : ℝ)*p.coeff 0+((((5/6) : ℚ) : ℝ)*p.coeff 1+((((2/3) : ℚ) : ℝ)*p.coeff 2+((((1/2) : ℚ) : ℝ)*p.coeff 3+((((1/3) : ℚ) : ℝ)*p.coeff 4+((((1/6) : ℚ) : ℝ)*p.coeff 5+(((0 : ℚ) : ℝ)*p.coeff 6+((((-1/6) : ℚ) : ℝ)*p.coeff 7+((((-1/3) : ℚ) : ℝ)*p.coeff 8+((((-1/2) : ℚ) : ℝ)*p.coeff 9+((((-2/3) : ℚ) : ℝ)*p.coeff 10+((((-5/6) : ℚ) : ℝ)*p.coeff 11+(((-1 : ℚ) : ℝ)*p.coeff 12+(0))))))))))))) := by
  simp only [bernsteinCoefficients,Fin.sum_univ_succ]
  rfl

theorem bernstein_model11 : bernsteinCoefficients gapQuotient 11=v1422 := by
  rw [bernstein_formula11,←quotient_model]
  norm_num [RealPoly.coeff_toPolynomial,p99,v17,v33,v423,v1143,v1144,v1169,v1172,v1173,v1175,v1178,v1179,v1181,v1184,v1186,v1189,v1190,v1192,v1195,v1196,v1198,v1201,v1405,v1406,v1407,v1408,v1409,v1410,v1411,v1412,v1413,v1414,v1415,v1416,v1417,v1418,v1419,v1420,v1421,v1422] <;> ring_nf <;> rfl

theorem positive11 : 0 < bernsteinCoefficients gapQuotient 11 := by
  rw [bernstein_model11]
  exact Box.positive_of_contains h1422 (by decide +kernel)

theorem bernstein_formula12 (p : Polynomial ℝ) : bernsteinCoefficients p 12=((1 : ℚ) : ℝ)*p.coeff 0+(((1 : ℚ) : ℝ)*p.coeff 1+(((1 : ℚ) : ℝ)*p.coeff 2+(((1 : ℚ) : ℝ)*p.coeff 3+(((1 : ℚ) : ℝ)*p.coeff 4+(((1 : ℚ) : ℝ)*p.coeff 5+(((1 : ℚ) : ℝ)*p.coeff 6+(((1 : ℚ) : ℝ)*p.coeff 7+(((1 : ℚ) : ℝ)*p.coeff 8+(((1 : ℚ) : ℝ)*p.coeff 9+(((1 : ℚ) : ℝ)*p.coeff 10+(((1 : ℚ) : ℝ)*p.coeff 11+(((1 : ℚ) : ℝ)*p.coeff 12+(0))))))))))))) := by
  simp only [bernsteinCoefficients,Fin.sum_univ_succ]
  rfl

theorem bernstein_model12 : bernsteinCoefficients gapQuotient 12=v1440 := by
  rw [bernstein_formula12,←quotient_model]
  norm_num [RealPoly.coeff_toPolynomial,p99,v17,v33,v1143,v1144,v1147,v1151,v1155,v1159,v1163,v1167,v1423,v1424,v1425,v1426,v1427,v1428,v1429,v1430,v1431,v1432,v1433,v1434,v1435,v1436,v1437,v1438,v1439,v1440] <;> ring_nf <;> rfl

theorem positive12 : 0 < bernsteinCoefficients gapQuotient 12 := by
  rw [bernstein_model12]
  exact Box.positive_of_contains h1440 (by decide +kernel)

theorem bernstein_positive (i : Fin 13) : 0 < bernsteinCoefficients gapQuotient i := by
  fin_cases i
  · exact positive0
  · exact positive1
  · exact positive2
  · exact positive3
  · exact positive4
  · exact positive5
  · exact positive6
  · exact positive7
  · exact positive8
  · exact positive9
  · exact positive10
  · exact positive11
  · exact positive12

end QuotientArithmetic
theorem gapQuotient_positive (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) : 0 < gapQuotient.eval t :=
  positive_of_bernstein _ gapQuotient_degree QuotientArithmetic.bernstein_positive ht

end Coulomb8

#print axioms Coulomb8.gapQuotient_positive
