/-
  Part Cons of the tie (C14) on `f2-examples/e2-cells-stream.kompile.kore`, test/TieE2CellsStream.lean: the sections
  `--split` puts here, in the tie's namespace. A test file imports no test file, so this one
  repeats the literals and the definitions and facts it reads. Written by
  `test/constructs/tiegen.py e2-cells-stream --split`; run from the package root:
  `lake env lean -j1 test/TieE2CellsStreamCons.lean`.

  Measured alone (LEAN_NUM_THREADS=1, `lake env lean -j1`, a 12G memory scope): 396 s, peak
  1.9 GiB.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE2CellsStream

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e2-cells-stream.kompile.kore"
definition_of defn from "f2-examples/e2-cells-stream.kompile.kore"
user_axioms U from "f2-examples/e2-cells-stream.kompile.kore" module "E2-CELLS-STREAM"
user_axioms PreludeKseq from "f2-examples/e2-cells-stream.kompile.kore" module "KSEQ"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-! ## The constructor sentences: functional, subsort, injectivity, distinctness -/

/-- The constructor sentences `tchConsB` decides, in text order. -/
noncomputable def consText : List AxiomDecl :=
  [U.ax4, U.ax5, U.ax6, U.ax7, U.ax8, U.ax9, U.ax10, U.ax11, U.ax12, U.ax13, U.ax14, U.ax15,
   U.ax16, U.ax17, U.ax18, U.ax19, U.ax20, U.ax21, U.ax22, U.ax23, U.ax24, U.ax25, U.ax26, U.ax27,
   U.ax28, U.ax29, U.ax30, U.ax31, U.ax32, U.ax33, U.ax34, U.ax35, U.ax36, U.ax37, U.ax38, U.ax39,
   U.ax40, U.ax41, U.ax42, U.ax43, U.ax44, U.ax45, U.ax46, U.ax47, U.ax48, U.ax49, U.ax50, U.ax51,
   U.ax52, U.ax53, U.ax54, U.ax55, U.ax56, U.ax57, U.ax58, U.ax59, U.ax60, U.ax61, U.ax62, U.ax63,
   U.ax64, U.ax65, U.ax66, U.ax67, U.ax68, U.ax69, U.ax70, U.ax71, U.ax72, U.ax73, U.ax74, U.ax75,
   U.ax76, U.ax77, U.ax78, U.ax79, U.ax80, U.ax81, U.ax82, U.ax83, U.ax84, U.ax85, U.ax86, U.ax87,
   U.ax88, U.ax89, U.ax90, U.ax91, U.ax92, U.ax93, U.ax94, U.ax95, U.ax96, U.ax97, U.ax98, U.ax99,
   U.ax100, U.ax101, U.ax102, U.ax103, U.ax104, U.ax105, U.ax106, U.ax107, U.ax108, U.ax109,
   U.ax110, U.ax111, U.ax112, U.ax113, U.ax114, U.ax115, U.ax116, U.ax117, U.ax118, U.ax119,
   U.ax120, U.ax121, U.ax122, U.ax123, U.ax124, U.ax125, U.ax126, U.ax127, U.ax128, U.ax129,
   U.ax130, U.ax131, U.ax132, U.ax133, U.ax134, U.ax135, U.ax136, U.ax137, U.ax138, U.ax139,
   U.ax140, U.ax141, U.ax142, U.ax143, U.ax144, U.ax145, U.ax146, U.ax147, U.ax148, U.ax149,
   U.ax150, U.ax151, U.ax152, U.ax153, U.ax154, U.ax155, U.ax156, U.ax157, U.ax158, U.ax159,
   U.ax160, U.ax161, U.ax162, U.ax163, U.ax164, U.ax165, U.ax166, U.ax167, U.ax168, U.ax169,
   U.ax170, U.ax171, U.ax172, U.ax173, U.ax174, U.ax175, U.ax176, U.ax177, U.ax178, U.ax179,
   U.ax180, U.ax181, U.ax182, U.ax183, U.ax184, U.ax185, U.ax186, U.ax187, U.ax188, U.ax189,
   U.ax190, U.ax191, U.ax192, U.ax193, U.ax194, U.ax195, U.ax196, U.ax197, U.ax198, U.ax199,
   U.ax200, U.ax201, U.ax202, U.ax203, U.ax204, U.ax205, U.ax206, U.ax207, U.ax208, U.ax209,
   U.ax210, U.ax211, U.ax212, U.ax213, U.ax214, U.ax215, U.ax216, U.ax217, U.ax218, U.ax219,
   U.ax220, U.ax221, U.ax222, U.ax223, U.ax224, U.ax225, U.ax226, U.ax227, U.ax228, U.ax229,
   U.ax230, U.ax231, U.ax232, U.ax233, U.ax234, U.ax235, U.ax236, U.ax237, U.ax238, U.ax239,
   U.ax240, U.ax241, U.ax242, U.ax243, U.ax244, U.ax245, U.ax246, U.ax247, U.ax248, U.ax249,
   U.ax250, U.ax251, U.ax252, U.ax253, U.ax254, U.ax255, U.ax256, U.ax257, U.ax258, U.ax259,
   U.ax260, U.ax261, U.ax262, U.ax263, U.ax264, U.ax265, U.ax266, U.ax267, U.ax268, U.ax269,
   U.ax270, U.ax271, U.ax272, U.ax273, U.ax274, U.ax275, U.ax276, U.ax277, U.ax278, U.ax279,
   U.ax280, U.ax281, U.ax282, U.ax283, U.ax284, U.ax285, U.ax286, U.ax287, U.ax288, U.ax289,
   U.ax290, U.ax291, U.ax292, U.ax293, U.ax294, U.ax295, U.ax296, U.ax297, U.ax298, U.ax299,
   U.ax300, U.ax301, U.ax302, U.ax303, U.ax304, U.ax305, U.ax306, U.ax307, U.ax308, U.ax309,
   U.ax310, U.ax311, U.ax312, U.ax313, U.ax314, U.ax315, U.ax316, U.ax317, U.ax318, U.ax319,
   U.ax320, U.ax321, U.ax322, U.ax323, U.ax324, U.ax325, U.ax326, U.ax327, U.ax328, U.ax329,
   U.ax330, U.ax331, U.ax332, U.ax333, U.ax334, U.ax335, U.ax336, U.ax337, U.ax338, U.ax339,
   U.ax340, U.ax341, U.ax342, U.ax343, U.ax344, U.ax345, U.ax346, U.ax347, U.ax348, U.ax349,
   U.ax350, U.ax351, U.ax352, U.ax353, U.ax354, U.ax355, U.ax356, U.ax357, U.ax358, U.ax359,
   U.ax360, U.ax361, U.ax362, U.ax363, U.ax364, U.ax365, U.ax366, U.ax367, U.ax368, U.ax369,
   U.ax370, U.ax371, U.ax372, U.ax373, U.ax374, U.ax375, U.ax376, U.ax377, U.ax378, U.ax379,
   U.ax380, U.ax381, U.ax382, U.ax383, U.ax384, U.ax385, U.ax386, U.ax387, U.ax388, U.ax389,
   U.ax390, U.ax391, U.ax392, U.ax393, U.ax394, U.ax395, U.ax396, U.ax397, U.ax398, U.ax399,
   U.ax400, U.ax401, U.ax402, U.ax403, U.ax404, U.ax405, U.ax406, U.ax407, U.ax408, U.ax409,
   U.ax410, U.ax411, U.ax412, U.ax413, U.ax414, U.ax415, U.ax416, U.ax417, U.ax418, U.ax419,
   U.ax420, U.ax421, U.ax422, U.ax423, U.ax424, U.ax425, U.ax426, U.ax427, U.ax428, U.ax429,
   U.ax430, U.ax431, U.ax432, U.ax433, U.ax434, U.ax435, U.ax436, U.ax437, U.ax438, U.ax439,
   U.ax440, U.ax441, U.ax442, U.ax443, U.ax444, U.ax445, U.ax446, U.ax447, U.ax448, U.ax449,
   U.ax450, U.ax451, U.ax452, U.ax453, U.ax454, U.ax455, U.ax456, U.ax457, U.ax458, U.ax459,
   U.ax460, U.ax461, U.ax462, U.ax463, U.ax464, U.ax465, U.ax466, U.ax467, U.ax468, U.ax469,
   U.ax470, U.ax471, U.ax472, U.ax473, U.ax474, U.ax475, U.ax476, U.ax477, U.ax478, U.ax479,
   U.ax480, U.ax481, U.ax482, U.ax483, U.ax484, U.ax485, U.ax486, U.ax487, U.ax488, U.ax489,
   U.ax490, U.ax491, U.ax492, U.ax493, U.ax494, U.ax495, U.ax496, U.ax497, U.ax498, U.ax499,
   U.ax500, U.ax501, U.ax502, U.ax503, U.ax504, U.ax505, U.ax506, U.ax507, U.ax508, U.ax509,
   U.ax510, U.ax511, U.ax512, U.ax513, U.ax514, U.ax515, U.ax516, U.ax517, U.ax518, U.ax519,
   U.ax520, U.ax521, U.ax522, U.ax523, U.ax524, U.ax525, U.ax526, U.ax527, U.ax528, U.ax529,
   U.ax530, U.ax531, U.ax532, U.ax533, U.ax534, U.ax535, U.ax536, U.ax537, U.ax538, U.ax539,
   U.ax540, U.ax541, U.ax542, U.ax543, U.ax544, U.ax545, U.ax546, U.ax547, U.ax548, U.ax549,
   U.ax550, U.ax551, U.ax552, U.ax553, U.ax554, U.ax555, U.ax556, U.ax557, U.ax558, U.ax559,
   U.ax560, U.ax561, U.ax562, U.ax563, U.ax564, U.ax565, U.ax566, U.ax567, U.ax568, U.ax569,
   U.ax570, U.ax571, U.ax572, U.ax573, U.ax574, U.ax575, U.ax576, U.ax577, U.ax578, U.ax579,
   U.ax580, U.ax581, U.ax582, U.ax583, U.ax584, U.ax585, U.ax586, U.ax587, U.ax588, U.ax589,
   U.ax590, U.ax591, U.ax592, U.ax593, U.ax594, U.ax595, U.ax596, U.ax597, U.ax598, U.ax599,
   U.ax600, U.ax601, U.ax602, U.ax603, U.ax604, U.ax605, U.ax606, U.ax607, U.ax608, U.ax609,
   U.ax610, U.ax611, U.ax612, U.ax613, U.ax614, U.ax615, U.ax616, U.ax617, U.ax618, U.ax619,
   U.ax620, U.ax621, U.ax622, U.ax623, U.ax624, U.ax625, U.ax626, U.ax627, U.ax628, U.ax629,
   U.ax630, U.ax631, U.ax632, U.ax633, U.ax634, U.ax635, U.ax636, U.ax637, U.ax638, U.ax639,
   U.ax640, U.ax641, U.ax642, U.ax643, U.ax644, U.ax645, U.ax646, U.ax647, U.ax648, U.ax649,
   U.ax650, U.ax651, U.ax652, U.ax653, U.ax654, U.ax655, U.ax656, U.ax657, U.ax658, U.ax659,
   U.ax660, U.ax661, U.ax662, U.ax663, U.ax664, U.ax665, U.ax666, U.ax667, U.ax668, U.ax669,
   U.ax670, U.ax671, U.ax672, U.ax673, U.ax674, U.ax675, U.ax676, U.ax677, U.ax678, U.ax679,
   U.ax680, U.ax681, U.ax682, U.ax683, U.ax684, U.ax685, U.ax686, U.ax687, U.ax688, U.ax689,
   U.ax690, U.ax691, U.ax692, U.ax693, U.ax694, U.ax695, U.ax696, U.ax697, U.ax698, U.ax699,
   U.ax700, U.ax701, U.ax702, U.ax703, U.ax704, U.ax705, U.ax706, U.ax707, U.ax708, U.ax709,
   U.ax710, U.ax711, U.ax712, U.ax713, U.ax714, U.ax715, U.ax716, U.ax717, U.ax718, U.ax719,
   U.ax720, U.ax721, U.ax722, U.ax723, U.ax724, U.ax725, U.ax726, U.ax727, U.ax728, U.ax729,
   U.ax730, U.ax731, U.ax732, U.ax733, U.ax734, U.ax735, U.ax736, U.ax737, U.ax738, U.ax739,
   U.ax740, U.ax741, U.ax742, U.ax743, U.ax744, U.ax745, U.ax746, U.ax747, U.ax748, U.ax749,
   U.ax750, U.ax751, U.ax752, U.ax753, U.ax754, U.ax755, U.ax756, U.ax757, U.ax758, U.ax759,
   U.ax760, U.ax761, U.ax762, U.ax763, U.ax764, U.ax765, U.ax766, U.ax767, U.ax768, U.ax769,
   U.ax770, U.ax771, U.ax772, U.ax773, U.ax774, U.ax775, U.ax776, U.ax777, U.ax778, U.ax779,
   U.ax780, U.ax781, U.ax782, U.ax783, U.ax784, U.ax785, U.ax786, U.ax787, U.ax788, U.ax789,
   U.ax790, U.ax791, U.ax792, U.ax793, U.ax794, U.ax795, U.ax796, U.ax797, U.ax798, U.ax799,
   U.ax800, U.ax801, U.ax802, U.ax803, U.ax804, U.ax805, U.ax806, U.ax807, U.ax808, U.ax809,
   U.ax810, U.ax811, U.ax812, U.ax813, U.ax814, U.ax815, U.ax816, U.ax817, U.ax818, U.ax819,
   U.ax820, U.ax821, U.ax822, U.ax823, U.ax824, U.ax825, U.ax826, U.ax827, U.ax828, U.ax829,
   U.ax830, U.ax831, U.ax832, U.ax833, U.ax834, U.ax835, U.ax836, U.ax837, U.ax838, U.ax839,
   U.ax840, U.ax841, U.ax842, U.ax843, U.ax844, U.ax845, U.ax846, U.ax847, U.ax848, U.ax849,
   U.ax850, U.ax851, U.ax852, U.ax853, U.ax854, U.ax855, U.ax856, U.ax857, U.ax858, U.ax859,
   U.ax860, U.ax861, U.ax862, U.ax863, U.ax864, U.ax865, U.ax866, U.ax867, U.ax868, U.ax869,
   U.ax870, U.ax871, U.ax872, U.ax873, U.ax874, U.ax875, U.ax876, U.ax877, U.ax878, U.ax879,
   U.ax880, U.ax881, U.ax882, U.ax883, U.ax884, U.ax885, U.ax886, U.ax887, U.ax888, U.ax889,
   U.ax890, U.ax891, U.ax892, U.ax893, U.ax894, U.ax895, U.ax896, U.ax897, U.ax898, U.ax899,
   U.ax900, U.ax901, U.ax902, U.ax903, U.ax904, U.ax905, U.ax906, U.ax907, U.ax908, U.ax909,
   U.ax910, U.ax911, U.ax912, U.ax913, U.ax914, U.ax915, U.ax916, U.ax917, U.ax918, U.ax919,
   U.ax920, U.ax921, U.ax922, U.ax923, U.ax924, U.ax925, U.ax926, U.ax927, U.ax928, U.ax929,
   U.ax930, U.ax931, U.ax932, U.ax933, U.ax934, U.ax935, U.ax936, U.ax937, U.ax938, U.ax939,
   U.ax940, U.ax941, U.ax942, U.ax943, U.ax944, U.ax945, U.ax946, U.ax947, U.ax948, U.ax949,
   U.ax950, U.ax951, U.ax952, U.ax953, U.ax954, U.ax955, U.ax956, U.ax957, U.ax958, U.ax959,
   U.ax960, U.ax961, U.ax962, U.ax963, U.ax964, U.ax965, U.ax966, U.ax967, U.ax968, U.ax969,
   U.ax970, U.ax971, U.ax972, U.ax973, U.ax974, U.ax975, U.ax976, U.ax977, U.ax978, U.ax979,
   U.ax980, U.ax981, U.ax982, U.ax983, U.ax984, U.ax985, U.ax986, U.ax987, U.ax988, U.ax989,
   U.ax990, U.ax991, U.ax992, U.ax993, U.ax994, U.ax995, U.ax996, U.ax997, U.ax998, U.ax999,
   U.ax1000, U.ax1001, U.ax1002, U.ax1003, U.ax1004, U.ax1005, U.ax1006, U.ax1007, U.ax1008,
   U.ax1009, U.ax1010, U.ax1011, U.ax1012, U.ax1013, U.ax1014, U.ax1015, U.ax1016, U.ax1017,
   U.ax1018, U.ax1019, U.ax1020, U.ax1021, U.ax1022, U.ax1023, U.ax1024, U.ax1025, U.ax1026,
   U.ax1027, U.ax1028, U.ax1029, U.ax1030, U.ax1031, U.ax1032, U.ax1033, U.ax1034, U.ax1035,
   U.ax1036, U.ax1037, U.ax1038, U.ax1039, U.ax1040, U.ax1041, U.ax1042, U.ax1043, U.ax1044,
   U.ax1045, U.ax1046, U.ax1047, U.ax1048, U.ax1049, U.ax1050, U.ax1051, U.ax1052, U.ax1053,
   U.ax1054, U.ax1055, U.ax1056, U.ax1057, U.ax1058, U.ax1059, U.ax1060, U.ax1061, U.ax1062,
   U.ax1063, U.ax1064, U.ax1065, U.ax1066, U.ax1067, U.ax1068, U.ax1069, U.ax1070, U.ax1071,
   U.ax1072, U.ax1073, U.ax1074, U.ax1075, U.ax1076, U.ax1077, U.ax1078, U.ax1079, U.ax1080,
   U.ax1081, U.ax1082, U.ax1083, U.ax1084, U.ax1085, U.ax1086, U.ax1087, U.ax1088, U.ax1089,
   U.ax1090, U.ax1091, U.ax1092, U.ax1093, U.ax1094, U.ax1095, U.ax1096, U.ax1097, U.ax1098,
   U.ax1099, U.ax1100, U.ax1101, U.ax1102, U.ax1103, U.ax1104, U.ax1105, U.ax1106, U.ax1107,
   U.ax1108, U.ax1109, U.ax1110, U.ax1111, U.ax1112, U.ax1113, U.ax1114, U.ax1115, U.ax1116,
   U.ax1117, U.ax1118, U.ax1119, U.ax1120, U.ax1121, U.ax1122, U.ax1123, U.ax1124, U.ax1125,
   U.ax1126, U.ax1127, U.ax1128, U.ax1129, U.ax1130, U.ax1131, U.ax1132, U.ax1133, U.ax1134,
   U.ax1135, U.ax1136, U.ax1137, U.ax1138, U.ax1139, U.ax1140, U.ax1141, U.ax1142, U.ax1143,
   U.ax1144, U.ax1145, U.ax1146, U.ax1147, U.ax1148, U.ax1149, U.ax1150, U.ax1151, U.ax1152,
   U.ax1153, U.ax1154, U.ax1155, U.ax1156, U.ax1157, U.ax1158, U.ax1159, U.ax1160, U.ax1161,
   U.ax1162, U.ax1163, U.ax1164, U.ax1165, U.ax1166, U.ax1167, U.ax1168, U.ax1169, U.ax1170,
   U.ax1171, U.ax1172, U.ax1173, U.ax1174, U.ax1175, U.ax1176, U.ax1177, U.ax1178, U.ax1179,
   U.ax1180, U.ax1181, U.ax1182, U.ax1183, U.ax1184, U.ax1185, U.ax1186, U.ax1187, U.ax1188,
   U.ax1189, U.ax1190, U.ax1191, U.ax1192, U.ax1193, U.ax1194, U.ax1195, U.ax1196, U.ax1197,
   U.ax1198, U.ax1199, U.ax1200, U.ax1201, U.ax1202, U.ax1203, U.ax1204, U.ax1205, U.ax1206,
   U.ax1207, U.ax1208, U.ax1209, U.ax1210, U.ax1211, U.ax1212, U.ax1213, U.ax1214, U.ax1215,
   U.ax1216, U.ax1217, U.ax1218, U.ax1219, U.ax1220, U.ax1221, U.ax1222, U.ax1223, U.ax1224,
   U.ax1225, U.ax1226, U.ax1227, U.ax1228, U.ax1229, U.ax1230, U.ax1231, U.ax1232, U.ax1233,
   U.ax1234, U.ax1235, U.ax1236, U.ax1237, U.ax1238, U.ax1239, U.ax1240, U.ax1241, U.ax1242,
   U.ax1243, U.ax1244, U.ax1245, U.ax1246, U.ax1247, U.ax1248, U.ax1249, U.ax1250, U.ax1251,
   U.ax1252, U.ax1253, U.ax1254, U.ax1255, U.ax1256, U.ax1257, U.ax1258, U.ax1259, U.ax1260,
   U.ax1261, U.ax1262, U.ax1263, U.ax1264, U.ax1265, U.ax1266, U.ax1267, U.ax1268, U.ax1269,
   U.ax1270, U.ax1271, U.ax1272, U.ax1273, U.ax1274, U.ax1275, U.ax1276, U.ax1277, U.ax1278,
   U.ax1279, U.ax1280, U.ax1281, U.ax1282, U.ax1283, U.ax1284, U.ax1285, U.ax1286, U.ax1287,
   U.ax1288, U.ax1289, U.ax1290, U.ax1291, U.ax1292, U.ax1293, U.ax1294, U.ax1295, U.ax1296,
   U.ax1297, U.ax1298, U.ax1299, U.ax1300, U.ax1301, U.ax1302, U.ax1303, U.ax1304, U.ax1305,
   U.ax1306, U.ax1307, U.ax1308, U.ax1309, U.ax1310, U.ax1311, U.ax1312, U.ax1313, U.ax1314,
   U.ax1315, U.ax1316, U.ax1317, U.ax1318, U.ax1319, U.ax1320, U.ax1321, U.ax1322, U.ax1323,
   U.ax1324, U.ax1325, U.ax1326, U.ax1327, U.ax1328, U.ax1329, U.ax1330, U.ax1331, U.ax1332,
   U.ax1333, U.ax1334, U.ax1335, U.ax1336, U.ax1337, U.ax1338, U.ax1339, U.ax1340, U.ax1341,
   U.ax1342, U.ax1343, U.ax1344, U.ax1345, U.ax1346, U.ax1347, U.ax1348, U.ax1349, U.ax1350,
   U.ax1351, U.ax1352, U.ax1353, U.ax1354, U.ax1355, U.ax1356, U.ax1357, U.ax1358, U.ax1359,
   U.ax1360, U.ax1361, U.ax1362, U.ax1363, U.ax1364, U.ax1365, U.ax1366, U.ax1367, U.ax1368,
   U.ax1369, U.ax1370, U.ax1371, U.ax1372, U.ax1373, U.ax1374, U.ax1375, U.ax1376, U.ax1377,
   U.ax1378, U.ax1379, U.ax1380, U.ax1381, U.ax1382, U.ax1383, U.ax1384, U.ax1385, U.ax1386,
   U.ax1387, U.ax1388, U.ax1389, U.ax1390, U.ax1391, U.ax1392, U.ax1393, U.ax1394, U.ax1395,
   U.ax1396, U.ax1397, U.ax1398, U.ax1399, U.ax1400, U.ax1401, U.ax1402, U.ax1403, U.ax1404,
   U.ax1405, U.ax1406, U.ax1407, U.ax1408, U.ax1409, U.ax1410, U.ax1411, U.ax1412, U.ax1413,
   U.ax1414, U.ax1415, U.ax1416, U.ax1417, U.ax1418, U.ax1419, U.ax1420, U.ax1421, U.ax1422,
   U.ax1423, U.ax1424, U.ax1425, U.ax1426, U.ax1427, U.ax1428, U.ax1429, U.ax1430, U.ax1431,
   U.ax1432, U.ax1433, U.ax1434, U.ax1435, U.ax1436, U.ax1437, U.ax1438, U.ax1439, U.ax1440,
   U.ax1441, U.ax1442, U.ax1443, U.ax1444, U.ax1445, U.ax1446, U.ax1447, U.ax1448, U.ax1449,
   U.ax1450, U.ax1451, U.ax1452, U.ax1453, U.ax1454, U.ax1455, U.ax1456, U.ax1457, U.ax1458,
   U.ax1459, U.ax1460, U.ax1461, U.ax1462, U.ax1463, U.ax1464, U.ax1465, U.ax1466, U.ax1467,
   U.ax1468, U.ax1469, U.ax1470, U.ax1471, U.ax1472, U.ax1473, U.ax1474, U.ax1475, U.ax1476,
   U.ax1477, U.ax1478, U.ax1479, U.ax1480, U.ax1481, U.ax1482, U.ax1483, U.ax1484, U.ax1485,
   U.ax1486, U.ax1487, U.ax1488, U.ax1489, U.ax1490, U.ax1491, U.ax1492, U.ax1493, U.ax1494,
   U.ax1495, U.ax1496, U.ax1497, U.ax1498, U.ax1499, U.ax1500, U.ax1501, U.ax1502, U.ax1503,
   U.ax1504, U.ax1505, U.ax1506, U.ax1507, U.ax1508, U.ax1509, U.ax1510, U.ax1511, U.ax1512,
   U.ax1513, U.ax1514, U.ax1515, U.ax1516, U.ax1517, U.ax1518, U.ax1519, U.ax1520, U.ax1521,
   U.ax1522, U.ax1523, U.ax1524, U.ax1525, U.ax1526, U.ax1527, U.ax1528, U.ax1529, U.ax1530,
   U.ax1531, U.ax1532, U.ax1533, U.ax1534, U.ax1535, U.ax1536, U.ax1537, U.ax1538, U.ax1539,
   U.ax1540, U.ax1541, U.ax1542, U.ax1543, U.ax1544, U.ax1545, U.ax1546, U.ax1547, U.ax1548,
   U.ax1549, U.ax1550, U.ax1551, U.ax1552, U.ax1553, U.ax1554, U.ax1555, U.ax1556, U.ax1557,
   U.ax1558, U.ax1559, U.ax1560, U.ax1561, U.ax1562, U.ax1563, U.ax1564, U.ax1565, U.ax1566,
   U.ax1567, U.ax1568, U.ax1569, U.ax1570, U.ax1571, U.ax1572, U.ax1573, U.ax1574, U.ax1575,
   U.ax1576, U.ax1577, U.ax1578, U.ax1579, U.ax1580, U.ax1581, U.ax1582, U.ax1583, U.ax1584,
   U.ax1585, U.ax1586, U.ax1587, U.ax1588, U.ax1589, U.ax1590, U.ax1591, U.ax1592, U.ax1593,
   U.ax1594, U.ax1595, U.ax1596, U.ax1597, U.ax1598, U.ax1599, U.ax1600, U.ax1601, U.ax1602,
   U.ax1603, U.ax1604, U.ax1605, U.ax1606, U.ax1607, U.ax1608, U.ax1609, U.ax1610, U.ax1611,
   U.ax1612, U.ax1613, U.ax1614, U.ax1615, U.ax1616, U.ax1617, U.ax1618, U.ax1619, U.ax1620,
   U.ax1621, U.ax1622, U.ax1623, U.ax1624, U.ax1625, U.ax1626, U.ax1627, U.ax1628, U.ax1629,
   U.ax1630, U.ax1631, U.ax1632, U.ax1633, U.ax1634, U.ax1635, U.ax1636, U.ax1637, U.ax1638,
   U.ax1639, U.ax1640, U.ax1641, U.ax1642, U.ax1643, U.ax1644, U.ax1645, U.ax1646, U.ax1647,
   U.ax1648, U.ax1649, U.ax1650, U.ax1651, U.ax1652, U.ax1653, U.ax1654, U.ax1655, U.ax1656,
   U.ax1657, U.ax1658, U.ax1659, U.ax1660, U.ax1661, U.ax1662, U.ax1663, U.ax1664, U.ax1665,
   U.ax1666, U.ax1667, U.ax1668, U.ax1669, U.ax1670, U.ax1671, U.ax1672, U.ax1673, U.ax1674,
   U.ax1675, U.ax1676, U.ax1677, U.ax1678, U.ax1679, U.ax1680, U.ax1681, U.ax1682, U.ax1683,
   U.ax1684, U.ax1685, U.ax1686, U.ax1687, U.ax1688, U.ax1689, U.ax1690, U.ax1691, U.ax1692,
   U.ax1693, U.ax1694, U.ax1695, U.ax1696, U.ax1697, U.ax1698, U.ax1699, U.ax1700, U.ax1701,
   U.ax1702, U.ax1703, U.ax1704, U.ax1705, U.ax1706, U.ax1707, U.ax1708, U.ax1709, U.ax1710,
   U.ax1711, U.ax1712, U.ax1713, U.ax1714, U.ax1715, U.ax1716, U.ax1717, U.ax1718, U.ax1719,
   U.ax1720, U.ax1721, U.ax1722, U.ax1723, U.ax1724, U.ax1725, U.ax1726, U.ax1727, U.ax1728,
   U.ax1729, U.ax1730, U.ax1731, U.ax1732, U.ax1733, U.ax1734, U.ax1735, U.ax1736, U.ax1737,
   U.ax1738, U.ax1739, U.ax1740, U.ax1741, U.ax1742, U.ax1743, U.ax1744, U.ax1745, U.ax1746,
   U.ax1747, U.ax1748, U.ax1749, U.ax1750, U.ax1751, U.ax1752, U.ax1753, U.ax1754, U.ax1755,
   U.ax1756, U.ax1757, U.ax1758, U.ax1759, U.ax1760, U.ax1761, U.ax1762, U.ax1763, U.ax1764,
   U.ax1765, U.ax1766, U.ax1767, U.ax1768, U.ax1769, U.ax1770, U.ax1771, U.ax1772, U.ax1773,
   U.ax1774, U.ax1775, U.ax1776, U.ax1777, U.ax1778, U.ax1779, U.ax1780, U.ax1781, U.ax1782,
   U.ax1783, U.ax1784, U.ax1785, U.ax1786, U.ax1787, U.ax1788, U.ax1789, U.ax1790, U.ax1791,
   U.ax1792, U.ax1793, U.ax1794, U.ax1795, U.ax1796, U.ax1797, U.ax1798, U.ax1799, U.ax1800,
   U.ax1801, U.ax1802, U.ax1803, U.ax1804, U.ax1805, U.ax1806, U.ax1807, U.ax1808, U.ax1809,
   U.ax1810, U.ax1811, U.ax1812, U.ax1813, U.ax1814, U.ax1815, U.ax1816, U.ax1817, U.ax1818,
   U.ax1819, U.ax1820, U.ax1821, U.ax1822, U.ax1823, U.ax1824, U.ax1825, U.ax1826, U.ax1827,
   U.ax1828, U.ax1829, U.ax1830, U.ax1831, U.ax1832, U.ax1833, U.ax1834, U.ax1835, U.ax1836,
   U.ax1837, U.ax1838, U.ax1839, U.ax1840, U.ax1841, U.ax1842, U.ax1843, U.ax1844, U.ax1845,
   U.ax1846, U.ax1847, U.ax1848, U.ax1849, U.ax1850, U.ax1851, U.ax1852, U.ax1853, U.ax1854,
   U.ax1855, U.ax1856, U.ax1857, U.ax1858, U.ax1859, U.ax1860, U.ax1861, U.ax1862, U.ax1863,
   U.ax1864, U.ax1865, U.ax1866, U.ax1867, U.ax1868, U.ax1869, U.ax1870, U.ax1871, U.ax1872,
   U.ax1873, U.ax1874, U.ax1875, U.ax1876, U.ax1877, U.ax1878, U.ax1879, U.ax1880, U.ax1881,
   U.ax1882, U.ax1883, U.ax1884, U.ax1885, U.ax1886, U.ax1887, U.ax1888, U.ax1889, U.ax1890,
   U.ax1891, U.ax1892, U.ax1893, U.ax1894, U.ax1895, U.ax1896, U.ax1897, U.ax1898, U.ax1899,
   U.ax1900, U.ax1901, U.ax1902, U.ax1903, U.ax1904, U.ax1905, U.ax1906, U.ax1907, U.ax1908,
   U.ax1909, U.ax1910, U.ax1911, U.ax1912, U.ax1913, U.ax1914, U.ax1915, U.ax1916, U.ax1917,
   U.ax1918, U.ax1919, U.ax1920, U.ax1921, U.ax1922, U.ax1923, U.ax1924, U.ax1925, U.ax1926,
   U.ax1927, U.ax1928, U.ax1929, U.ax1930, U.ax1931, U.ax1932, U.ax1933, U.ax1934, U.ax1935,
   U.ax1936, U.ax1937, U.ax1938, U.ax1939, U.ax1940, U.ax1941, U.ax1942, U.ax1943, U.ax1944,
   U.ax1945, U.ax1946, U.ax1947, U.ax1948, U.ax1949, U.ax1950, U.ax1951, U.ax1952, U.ax1953,
   U.ax1954, U.ax1955, U.ax1956, U.ax1957, U.ax1958, U.ax1959, U.ax1960, U.ax1961, U.ax1962,
   U.ax1963, U.ax1964, U.ax1965, U.ax1966, U.ax1967, U.ax1968, U.ax1969, U.ax1970, U.ax1971,
   U.ax1972, U.ax1973, U.ax1974, U.ax1975, U.ax1976, U.ax1977, U.ax1978, U.ax1979, U.ax1980,
   U.ax1981, U.ax1982, U.ax1983, U.ax1984, U.ax1985, U.ax1986, U.ax1987, U.ax1988, U.ax1989,
   U.ax1990, U.ax1991, U.ax1992, U.ax1993, U.ax1994, U.ax1995, U.ax1996, U.ax1997, U.ax1998,
   U.ax1999, U.ax2000, U.ax2001, U.ax2002, U.ax2003, U.ax2004, U.ax2005, U.ax2006, U.ax2007,
   U.ax2008, U.ax2009, U.ax2010, U.ax2011, U.ax2012, U.ax2013, U.ax2014, U.ax2015, U.ax2016,
   U.ax2017, U.ax2018, U.ax2019, U.ax2020, U.ax2021, U.ax2022, U.ax2023, U.ax2024, U.ax2025,
   U.ax2026, U.ax2027, U.ax2028, U.ax2029, U.ax2030, U.ax2031, U.ax2032, U.ax2033, U.ax2034,
   U.ax2035, U.ax2036, U.ax2037, U.ax2038, U.ax2039, U.ax2040, U.ax2041, U.ax2042, U.ax2043,
   U.ax2044, U.ax2045, U.ax2046, U.ax2047, U.ax2048, U.ax2049, U.ax2050, U.ax2051, U.ax2052,
   U.ax2053, U.ax2054, U.ax2055, U.ax2056, U.ax2057, U.ax2058, U.ax2059, U.ax2060, U.ax2061,
   U.ax2062, U.ax2063, U.ax2064, U.ax2065, U.ax2066, U.ax2067, U.ax2068, U.ax2069, U.ax2070,
   U.ax2071, U.ax2072, U.ax2073, U.ax2074, U.ax2075, U.ax2076, U.ax2077, U.ax2078, U.ax2079,
   U.ax2080, U.ax2081, U.ax2082, U.ax2083, U.ax2084, U.ax2085, U.ax2086, U.ax2087, U.ax2088,
   U.ax2089, U.ax2090, U.ax2091, U.ax2092, U.ax2093, U.ax2094, U.ax2095, U.ax2096, U.ax2097,
   U.ax2098, U.ax2099, U.ax2100, U.ax2101, U.ax2102, U.ax2103, U.ax2104, U.ax2105, U.ax2106,
   U.ax2107, U.ax2108, U.ax2109, U.ax2110, U.ax2111, U.ax2112, U.ax2113, U.ax2114, U.ax2115,
   U.ax2116, U.ax2117, U.ax2118, U.ax2119, U.ax2120, U.ax2121, U.ax2122, U.ax2123, U.ax2124,
   U.ax2125, U.ax2126, U.ax2127, U.ax2128, U.ax2129, U.ax2130, U.ax2131, U.ax2132, U.ax2133,
   U.ax2134, U.ax2135, U.ax2136, U.ax2137, U.ax2138, U.ax2139, U.ax2140, U.ax2141, U.ax2142,
   U.ax2143, U.ax2144, U.ax2145, U.ax2146, U.ax2147, U.ax2148, U.ax2149, U.ax2150, U.ax2151,
   U.ax2152, U.ax2153, U.ax2154, U.ax2155, U.ax2156, U.ax2157, U.ax2158, U.ax2159, U.ax2160,
   U.ax2161, U.ax2162, U.ax2163, U.ax2164, U.ax2165, U.ax2166, U.ax2167, U.ax2168, U.ax2169,
   U.ax2170, U.ax2171, U.ax2172, U.ax2173, U.ax2174, U.ax2175, U.ax2176, U.ax2177, U.ax2178,
   U.ax2179, U.ax2180, U.ax2181, U.ax2182, U.ax2183, U.ax2184, U.ax2185, U.ax2186, U.ax2187,
   U.ax2188, U.ax2189, U.ax2190, U.ax2191, U.ax2192, U.ax2193, U.ax2194, U.ax2195, U.ax2196,
   U.ax2197, U.ax2198, U.ax2199, U.ax2200, U.ax2201, U.ax2202, U.ax2203, U.ax2204, U.ax2205,
   U.ax2206, U.ax2207, U.ax2208, U.ax2209, U.ax2210, U.ax2211, U.ax2212, U.ax2213, U.ax2214,
   U.ax2215, U.ax2216, U.ax2217, U.ax2218, U.ax2219, U.ax2220, U.ax2221, U.ax2222, U.ax2223,
   U.ax2224, U.ax2225, U.ax2226, U.ax2227, U.ax2228, U.ax2229, U.ax2230, U.ax2231, U.ax2232,
   U.ax2233, U.ax2234, U.ax2235, U.ax2236, U.ax2237, U.ax2238, U.ax2239, U.ax2240, U.ax2241,
   U.ax2242, U.ax2243, U.ax2244, U.ax2245, U.ax2246, U.ax2247, U.ax2248, U.ax2249, U.ax2250,
   U.ax2251, U.ax2252, U.ax2253, U.ax2254, U.ax2255, U.ax2256, U.ax2257, U.ax2258, U.ax2259,
   U.ax2260, U.ax2261, U.ax2262, U.ax2263, U.ax2264, U.ax2265, U.ax2266, U.ax2267, U.ax2268,
   U.ax2269, U.ax2270, U.ax2271, U.ax2272, U.ax2273, U.ax2274, U.ax2275, U.ax2276, U.ax2277,
   U.ax2278, U.ax2279, U.ax2280, U.ax2281, U.ax2282, U.ax2283, U.ax2284, U.ax2285, U.ax2286,
   U.ax2287, U.ax2288, U.ax2289, U.ax2290, U.ax2291, U.ax2292, U.ax2293, U.ax2294, U.ax2295,
   U.ax2296, U.ax2297, U.ax2298, U.ax2299, U.ax2300, U.ax2301, U.ax2302, U.ax2303, U.ax2304,
   U.ax2305, U.ax2306, U.ax2307, U.ax2308, U.ax2309, U.ax2310, U.ax2311, U.ax2312, U.ax2313,
   U.ax2314, U.ax2315, U.ax2316, U.ax2317, U.ax2318, U.ax2319, U.ax2320, U.ax2321, U.ax2322,
   U.ax2323, U.ax2324, U.ax2325, U.ax2326, U.ax2327, U.ax2328, U.ax2329, U.ax2330, U.ax2331,
   U.ax2332, U.ax2333, U.ax2334, U.ax2335, U.ax2336, U.ax2337, U.ax2338, U.ax2339, U.ax2340,
   U.ax2341, U.ax2342, U.ax2343, U.ax2344, U.ax2345, U.ax2346, U.ax2347, U.ax2348, U.ax2349,
   U.ax2350, U.ax2351, U.ax2352, U.ax2353, U.ax2354, U.ax2355, U.ax2356, U.ax2357, U.ax2358,
   U.ax2359, U.ax2360, U.ax2361, U.ax2362, U.ax2363, U.ax2364, U.ax2365, U.ax2366, U.ax2367,
   U.ax2368, U.ax2369, U.ax2370, U.ax2371, U.ax2372, U.ax2373, U.ax2374, U.ax2375, U.ax2376,
   U.ax2377, U.ax2378, U.ax2379, U.ax2380, U.ax2381, U.ax2382, U.ax2383, U.ax2384, U.ax2385,
   U.ax2386, U.ax2387, U.ax2388, U.ax2389, U.ax2390, U.ax2391, U.ax2392, U.ax2393, U.ax2394,
   U.ax2395, U.ax2396, U.ax2397, U.ax2398, U.ax2399, U.ax2400, U.ax2401, U.ax2402, U.ax2403,
   U.ax2404, U.ax2405, U.ax2406, U.ax2407, U.ax2408, U.ax2409, U.ax2410, U.ax2411, U.ax2412,
   U.ax2413, U.ax2414, U.ax2415, U.ax2416, U.ax2417, U.ax2418, U.ax2419, U.ax2420, U.ax2421,
   U.ax2422, U.ax2423, U.ax2424, U.ax2425, U.ax2426, U.ax2427, U.ax2428, U.ax2429, U.ax2430,
   U.ax2431, U.ax2432, U.ax2433, U.ax2434, U.ax2435, U.ax2436, U.ax2437, U.ax2438, U.ax2439,
   U.ax2440, U.ax2441, U.ax2442, U.ax2443, U.ax2444, U.ax2445, U.ax2446, U.ax2447, U.ax2448,
   U.ax2449, U.ax2450, U.ax2451, U.ax2452, U.ax2453, U.ax2454, U.ax2455, U.ax2456, U.ax2457,
   U.ax2458, U.ax2459, U.ax2460, U.ax2461, U.ax2462, U.ax2463, U.ax2464, U.ax2465, U.ax2466,
   U.ax2467, U.ax2468, U.ax2469, U.ax2470, U.ax2471, U.ax2472, U.ax2473, U.ax2474, U.ax2475,
   U.ax2476, U.ax2477, U.ax2478, U.ax2479, U.ax2480, U.ax2481, U.ax2482, U.ax2483, U.ax2484,
   U.ax2485, U.ax2486, U.ax2487, U.ax2488, U.ax2489, U.ax2490, U.ax2491, U.ax2492, U.ax2493,
   U.ax2494, U.ax2495, U.ax2496, U.ax2497, U.ax2498, U.ax2499, U.ax2500, U.ax2501, U.ax2502,
   U.ax2503, U.ax2504, U.ax2505, U.ax2506, U.ax2507, U.ax2508, U.ax2509, U.ax2510, U.ax2511,
   U.ax2512, U.ax2513, U.ax2514, U.ax2515, U.ax2516, U.ax2517, U.ax2518, U.ax2519, U.ax2520,
   U.ax2521, U.ax2522, U.ax2523, U.ax2524, U.ax2525, U.ax2526, U.ax2527, U.ax2528, U.ax2529,
   U.ax2530, U.ax2531, U.ax2532, U.ax2533, U.ax2534, U.ax2535, U.ax2536, U.ax2537, U.ax2538,
   U.ax2539, U.ax2540, U.ax2541, U.ax2542, U.ax2543, U.ax2544, U.ax2545, U.ax2546, U.ax2547,
   U.ax2548, U.ax2549, U.ax2550, U.ax2551, U.ax2552, U.ax2553, U.ax2554, U.ax2555, U.ax2556,
   U.ax2557, U.ax2558, U.ax2559, U.ax2560, U.ax2561, U.ax2562, U.ax2563, U.ax2564, U.ax2565,
   U.ax2566, U.ax2567, U.ax2568, U.ax2569, U.ax2570, U.ax2571, U.ax2572, U.ax2573, U.ax2574,
   U.ax2575, U.ax2576, U.ax2577, U.ax2578, U.ax2579, U.ax2580, U.ax2581, U.ax2582, U.ax2583,
   U.ax2584, U.ax2585, U.ax2586, U.ax2587, U.ax2588, U.ax2589, U.ax2590, U.ax2591, U.ax2592,
   U.ax2593, U.ax2594, U.ax2595, U.ax2596, U.ax2597, U.ax2598, U.ax2599, U.ax2600, U.ax2601,
   U.ax2602, U.ax2605, U.ax2606, U.ax2607, U.ax2608, U.ax2609, U.ax2610, U.ax2611, U.ax2612,
   U.ax2617, U.ax2618, U.ax2619, U.ax2620, U.ax2623, U.ax2624, U.ax2628, U.ax2629, U.ax2630,
   U.ax2631, U.ax2632, U.ax2633, U.ax2634, U.ax2635, U.ax2636, U.ax2637, U.ax2638, U.ax2639,
   U.ax2640, U.ax2641, U.ax2642, U.ax2643, U.ax2701, U.ax2741, U.ax2742, U.ax2743, U.ax2744,
   U.ax2745]

theorem consE_0 : (((consText).drop 0).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_40 : (((consText).drop 40).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_80 : (((consText).drop 80).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_120 : (((consText).drop 120).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_160 : (((consText).drop 160).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_200 : (((consText).drop 200).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_240 : (((consText).drop 240).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_280 : (((consText).drop 280).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_320 : (((consText).drop 320).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_360 : (((consText).drop 360).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_400 : (((consText).drop 400).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_440 : (((consText).drop 440).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_480 : (((consText).drop 480).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_520 : (((consText).drop 520).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_560 : (((consText).drop 560).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_600 : (((consText).drop 600).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_640 : (((consText).drop 640).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_680 : (((consText).drop 680).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_720 : (((consText).drop 720).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_760 : (((consText).drop 760).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_800 : (((consText).drop 800).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_840 : (((consText).drop 840).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_880 : (((consText).drop 880).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_920 : (((consText).drop 920).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_960 : (((consText).drop 960).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_1000 : (((consText).drop 1000).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_1040 : (((consText).drop 1040).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_1080 : (((consText).drop 1080).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_1120 : (((consText).drop 1120).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_1160 : (((consText).drop 1160).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_1200 : (((consText).drop 1200).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_1240 : (((consText).drop 1240).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_1280 : (((consText).drop 1280).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_1320 : (((consText).drop 1320).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_1360 : (((consText).drop 1360).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_1400 : (((consText).drop 1400).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_1440 : (((consText).drop 1440).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_1480 : (((consText).drop 1480).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_1520 : (((consText).drop 1520).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_1560 : (((consText).drop 1560).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_1600 : (((consText).drop 1600).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_1640 : (((consText).drop 1640).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_1680 : (((consText).drop 1680).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_1720 : (((consText).drop 1720).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_1760 : (((consText).drop 1760).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_1800 : (((consText).drop 1800).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_1840 : (((consText).drop 1840).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_1880 : (((consText).drop 1880).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_1920 : (((consText).drop 1920).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_1960 : (((consText).drop 1960).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_2000 : (((consText).drop 2000).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_2040 : (((consText).drop 2040).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_2080 : (((consText).drop 2080).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_2120 : (((consText).drop 2120).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_2160 : (((consText).drop 2160).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_2200 : (((consText).drop 2200).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_2240 : (((consText).drop 2240).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_2280 : (((consText).drop 2280).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_2320 : (((consText).drop 2320).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_2360 : (((consText).drop 2360).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_2400 : (((consText).drop 2400).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_2440 : (((consText).drop 2440).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_2480 : (((consText).drop 2480).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_2520 : (((consText).drop 2520).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_2560 : (((consText).drop 2560).take 40).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem consE_2600 : ((consText).drop 2600).all (fun ad => tchConsB c ad.ax) = true := by decide +kernel
theorem cons_checked_hd : consText.all (fun ad => tchConsB c ad.ax) = true :=
  tieAll_whole (l := consText) (p := (fun ad => tchConsB c ad.ax)) <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 0) (n := 40) consE_0 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 40) (n := 40) consE_40 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 80) (n := 40) consE_80 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 120) (n := 40) consE_120 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 160) (n := 40) consE_160 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 200) (n := 40) consE_200 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 240) (n := 40) consE_240 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 280) (n := 40) consE_280 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 320) (n := 40) consE_320 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 360) (n := 40) consE_360 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 400) (n := 40) consE_400 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 440) (n := 40) consE_440 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 480) (n := 40) consE_480 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 520) (n := 40) consE_520 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 560) (n := 40) consE_560 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 600) (n := 40) consE_600 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 640) (n := 40) consE_640 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 680) (n := 40) consE_680 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 720) (n := 40) consE_720 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 760) (n := 40) consE_760 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 800) (n := 40) consE_800 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 840) (n := 40) consE_840 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 880) (n := 40) consE_880 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 920) (n := 40) consE_920 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 960) (n := 40) consE_960 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 1000) (n := 40) consE_1000 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 1040) (n := 40) consE_1040 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 1080) (n := 40) consE_1080 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 1120) (n := 40) consE_1120 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 1160) (n := 40) consE_1160 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 1200) (n := 40) consE_1200 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 1240) (n := 40) consE_1240 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 1280) (n := 40) consE_1280 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 1320) (n := 40) consE_1320 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 1360) (n := 40) consE_1360 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 1400) (n := 40) consE_1400 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 1440) (n := 40) consE_1440 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 1480) (n := 40) consE_1480 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 1520) (n := 40) consE_1520 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 1560) (n := 40) consE_1560 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 1600) (n := 40) consE_1600 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 1640) (n := 40) consE_1640 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 1680) (n := 40) consE_1680 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 1720) (n := 40) consE_1720 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 1760) (n := 40) consE_1760 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 1800) (n := 40) consE_1800 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 1840) (n := 40) consE_1840 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 1880) (n := 40) consE_1880 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 1920) (n := 40) consE_1920 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 1960) (n := 40) consE_1960 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 2000) (n := 40) consE_2000 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 2040) (n := 40) consE_2040 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 2080) (n := 40) consE_2080 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 2120) (n := 40) consE_2120 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 2160) (n := 40) consE_2160 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 2200) (n := 40) consE_2200 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 2240) (n := 40) consE_2240 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 2280) (n := 40) consE_2280 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 2320) (n := 40) consE_2320 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 2360) (n := 40) consE_2360 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 2400) (n := 40) consE_2400 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 2440) (n := 40) consE_2440 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 2480) (n := 40) consE_2480 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 2520) (n := 40) consE_2520 <|
    tieAll_range (l := consText) (p := (fun ad => tchConsB c ad.ax)) (a := 2560) (n := 40) consE_2560 <|
    consE_2600

theorem cons_checked : consText.all (fun ad => tieConsB c ad.ax) = true := tchConsB_all cons_checked_hd

theorem consT_0 : (((consText).drop 0).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_40 : (((consText).drop 40).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_80 : (((consText).drop 80).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_120 : (((consText).drop 120).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_160 : (((consText).drop 160).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_200 : (((consText).drop 200).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_240 : (((consText).drop 240).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_280 : (((consText).drop 280).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_320 : (((consText).drop 320).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_360 : (((consText).drop 360).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_400 : (((consText).drop 400).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_440 : (((consText).drop 440).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_480 : (((consText).drop 480).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_520 : (((consText).drop 520).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_560 : (((consText).drop 560).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_600 : (((consText).drop 600).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_640 : (((consText).drop 640).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_680 : (((consText).drop 680).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_720 : (((consText).drop 720).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_760 : (((consText).drop 760).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_800 : (((consText).drop 800).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_840 : (((consText).drop 840).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_880 : (((consText).drop 880).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_920 : (((consText).drop 920).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_960 : (((consText).drop 960).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_1000 : (((consText).drop 1000).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_1040 : (((consText).drop 1040).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_1080 : (((consText).drop 1080).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_1120 : (((consText).drop 1120).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_1160 : (((consText).drop 1160).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_1200 : (((consText).drop 1200).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_1240 : (((consText).drop 1240).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_1280 : (((consText).drop 1280).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_1320 : (((consText).drop 1320).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_1360 : (((consText).drop 1360).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_1400 : (((consText).drop 1400).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_1440 : (((consText).drop 1440).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_1480 : (((consText).drop 1480).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_1520 : (((consText).drop 1520).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_1560 : (((consText).drop 1560).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_1600 : (((consText).drop 1600).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_1640 : (((consText).drop 1640).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_1680 : (((consText).drop 1680).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_1720 : (((consText).drop 1720).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_1760 : (((consText).drop 1760).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_1800 : (((consText).drop 1800).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_1840 : (((consText).drop 1840).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_1880 : (((consText).drop 1880).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_1920 : (((consText).drop 1920).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_1960 : (((consText).drop 1960).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_2000 : (((consText).drop 2000).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_2040 : (((consText).drop 2040).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_2080 : (((consText).drop 2080).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_2120 : (((consText).drop 2120).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_2160 : (((consText).drop 2160).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_2200 : (((consText).drop 2200).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_2240 : (((consText).drop 2240).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_2280 : (((consText).drop 2280).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_2320 : (((consText).drop 2320).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_2360 : (((consText).drop 2360).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_2400 : (((consText).drop 2400).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_2440 : (((consText).drop 2440).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_2480 : (((consText).drop 2480).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_2520 : (((consText).drop 2520).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_2560 : (((consText).drop 2560).take 40).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem consT_2600 : ((consText).drop 2600).all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by decide +kernel
theorem cons_trS : consText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true :=
  tieAll_whole (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 0) (n := 40) consT_0 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 40) (n := 40) consT_40 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 80) (n := 40) consT_80 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 120) (n := 40) consT_120 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 160) (n := 40) consT_160 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 200) (n := 40) consT_200 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 240) (n := 40) consT_240 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 280) (n := 40) consT_280 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 320) (n := 40) consT_320 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 360) (n := 40) consT_360 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 400) (n := 40) consT_400 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 440) (n := 40) consT_440 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 480) (n := 40) consT_480 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 520) (n := 40) consT_520 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 560) (n := 40) consT_560 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 600) (n := 40) consT_600 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 640) (n := 40) consT_640 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 680) (n := 40) consT_680 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 720) (n := 40) consT_720 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 760) (n := 40) consT_760 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 800) (n := 40) consT_800 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 840) (n := 40) consT_840 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 880) (n := 40) consT_880 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 920) (n := 40) consT_920 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 960) (n := 40) consT_960 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 1000) (n := 40) consT_1000 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 1040) (n := 40) consT_1040 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 1080) (n := 40) consT_1080 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 1120) (n := 40) consT_1120 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 1160) (n := 40) consT_1160 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 1200) (n := 40) consT_1200 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 1240) (n := 40) consT_1240 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 1280) (n := 40) consT_1280 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 1320) (n := 40) consT_1320 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 1360) (n := 40) consT_1360 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 1400) (n := 40) consT_1400 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 1440) (n := 40) consT_1440 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 1480) (n := 40) consT_1480 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 1520) (n := 40) consT_1520 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 1560) (n := 40) consT_1560 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 1600) (n := 40) consT_1600 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 1640) (n := 40) consT_1640 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 1680) (n := 40) consT_1680 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 1720) (n := 40) consT_1720 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 1760) (n := 40) consT_1760 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 1800) (n := 40) consT_1800 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 1840) (n := 40) consT_1840 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 1880) (n := 40) consT_1880 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 1920) (n := 40) consT_1920 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 1960) (n := 40) consT_1960 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 2000) (n := 40) consT_2000 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 2040) (n := 40) consT_2040 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 2080) (n := 40) consT_2080 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 2120) (n := 40) consT_2120 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 2160) (n := 40) consT_2160 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 2200) (n := 40) consT_2200 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 2240) (n := 40) consT_2240 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 2280) (n := 40) consT_2280 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 2320) (n := 40) consT_2320 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 2360) (n := 40) consT_2360 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 2400) (n := 40) consT_2400 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 2440) (n := 40) consT_2440 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 2480) (n := 40) consT_2480 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 2520) (n := 40) consT_2520 <|
    tieAll_range (l := consText) (p := (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))) (a := 2560) (n := 40) consT_2560 <|
    consT_2600

/-- **E for the constructor sentences**: Γ entails each, for every H. -/
theorem cons_entailed (H : HookParams) : ∀ ad ∈ consText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  rw [of_decide_eq_true (List.all_eq_true.mp cons_trS ad had)]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  exact tieCons_entailed (c := cH H) (a := ad.ax)
    ((tieConsB_withHooks c H ad.ax).trans (List.all_eq_true.mp cons_checked ad had)) ad.index ad.module hI

end KCore.TieE2CellsStream

#check @KCore.TieE2CellsStream.cons_entailed
#print axioms KCore.TieE2CellsStream.cons_entailed
