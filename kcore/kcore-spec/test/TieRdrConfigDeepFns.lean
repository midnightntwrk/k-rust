/-
  Part Fns of the tie (C14) on `f2-examples/rdr-config-deep.kompile.kore`, test/TieRdrConfigDeep.lean: the sections
  `--split` puts here, in the tie's namespace. A test file imports no test file, so this one
  repeats the literals and the definitions and facts it reads. Written by
  `TIEGEN_PROBE_TIMEOUT=3000 python3 -I test/constructs/tiegen.py rdr-config-deep --split --cons-head
  --wf-parts --sig-chunk-first 13 --account-sorted --heads-literal --heads-codes --chunk 50
  --attrs-blocks 50 --decl-parts --fn-blocks 27 --absent-file --decl-syms-literal --nojunk-eq
  --nojunk-blocks 25`;
  run from the package root: `lake env lean -j1 test/TieRdrConfigDeepFns.lean`
  (130 s, peak 1.3 GiB under a 12 GiB scope with one Lean thread).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieRdrConfigDeep

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/rdr-config-deep.kompile.kore"
definition_of defn from "f2-examples/rdr-config-deep.kompile.kore"
user_axioms U from "f2-examples/rdr-config-deep.kompile.kore" module "RDR-CONFIG-DEEP"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-- Per class of the tie (`tieClasses`), the indices (`AxiomDecl.index`) of its sentences. -/
def classes : List (String × List Nat) :=
  [("function equation", [1102, 1103, 1104, 1105, 1106, 1107, 1108, 1109, 1110, 1111, 1112, 1113, 1114, 1115, 1116,
      1117, 1118, 1119, 1120, 1121, 1122, 1123, 1124, 1125, 1126, 1127, 1128, 1129, 1130, 1131,
      1132, 1133, 1134, 1135, 1136, 1137, 1138, 1139, 1140, 1141, 1142, 1143, 1144, 1145, 1146,
      1147, 1148, 1149, 1150, 1151, 1152, 1153, 1154, 1155, 1156, 1157, 1158, 1159, 1160, 1161,
      1162, 1163, 1164, 1165, 1166, 1167, 1168, 1169, 1170, 1171, 1172, 1173, 1174, 1175, 1176,
      1177, 1178, 1179, 1180, 1181, 1182, 1183, 1184, 1185, 1186, 1187, 1188, 1189, 1190, 1191,
      1192, 1193, 1194, 1195, 1196, 1197, 1198, 1199, 1200, 1201, 1202, 1203, 1204, 1205, 1206,
      1207, 1208, 1209, 1210, 1211, 1212, 1213, 1214, 1215, 1216, 1217, 1218, 1219, 1220, 1221,
      1222, 1223, 1224, 1225, 1226, 1227, 1228, 1229, 1230, 1231, 1232, 1233, 1234, 1235, 1236,
      1237, 1238, 1239, 1240, 1241, 1242, 1243, 1244, 1245, 1246, 1247, 1248, 1249, 1250, 1251,
      1252, 1253, 1254, 1255, 1256, 1257, 1258, 1259, 1260, 1261, 1262, 1263, 1264, 1265, 1266,
      1267, 1268, 1269, 1270, 1271, 1272, 1273, 1274, 1275, 1276, 1277, 1278, 1279, 1280, 1281,
      1282, 1283, 1284, 1285, 1286, 1287, 1288, 1289, 1290, 1291, 1292, 1293, 1294, 1295, 1296,
      1297, 1298, 1299, 1300, 1301, 1302, 1303, 1304, 1305, 1306, 1307, 1308, 1309, 1310, 1311,
      1312, 1313, 1314, 1315, 1316, 1317, 1318, 1319, 1320, 1321, 1322, 1323, 1324, 1325, 1326,
      1327, 1328, 1329, 1330, 1331, 1332, 1333, 1334, 1335, 1336, 1337, 1338, 1339, 1340, 1341,
      1342, 1343, 1344, 1345, 1346, 1347, 1348, 1349, 1350, 1351, 1352, 1353, 1354, 1355, 1356,
      1357, 1358, 1359, 1360, 1361, 1362, 1363, 1364, 1365, 1366, 1367, 1368, 1369, 1370, 1371,
      1372, 1373, 1374, 1375, 1376, 1377, 1378, 1379, 1380, 1381, 1382, 1383, 1384, 1385, 1386,
      1387, 1388, 1389, 1390, 1391, 1392, 1393, 1394, 1395, 1396, 1397, 1398, 1399, 1400, 1401,
      1402, 1403, 1404, 1405, 1406, 1407, 1408, 1409, 1410, 1411, 1412, 1413, 1414, 1415, 1416,
      1417, 1418, 1419, 1420, 1421, 1422, 1423, 1424, 1425, 1426, 1427, 1428, 1429, 1430, 1431,
      1432, 1433, 1434, 1435, 1436, 1437, 1438, 1439, 1440, 1441, 1442, 1443, 1444, 1445, 1446,
      1447, 1448, 1449, 1450, 1451, 1452, 1453, 1454, 1455, 1456, 1457, 1458, 1459, 1460, 1461,
      1462, 1463, 1464, 1465, 1466, 1467, 1468, 1469, 1470, 1471, 1472, 1473, 1474, 1475, 1476,
      1477, 1478, 1479, 1480, 1481, 1482, 1483, 1484, 1485, 1486, 1487, 1488, 1489, 1490, 1491,
      1492, 1493, 1494, 1495, 1496, 1497, 1498, 1499, 1500, 1501, 1502, 1503, 1504, 1505, 1506]),
   ("rewrite rule", []),
   ("priority equation", []),
   ("constructor functional", [273, 275, 277, 279, 281, 283, 285, 287, 289, 291, 293, 295, 297, 299, 301, 303, 305, 307,
      309, 311, 313, 315, 317, 319, 321, 323, 325, 327, 329, 331, 333, 335, 337, 339, 341, 343,
      345, 347, 349, 351, 353, 355, 357, 359, 361, 363, 365, 367, 369, 371, 373, 375, 377, 379,
      381, 383, 385, 387, 389, 391, 393, 395, 397, 399, 401, 403, 405, 407, 409, 411, 413, 415,
      417, 419, 421, 423, 425, 427, 429, 431, 433, 435, 437, 439, 441, 443, 445, 447, 449, 451,
      453, 455, 457, 459, 461, 463, 465, 467, 469, 471, 473, 475, 477, 479, 481, 483, 485, 487,
      489, 491, 493, 495, 497, 499, 501, 503, 505, 507, 509, 511, 513, 515, 517, 519, 521, 523,
      525, 527, 529, 531, 764, 765, 766, 767, 768, 769, 770, 771, 772, 773, 774, 775, 776, 777,
      778, 779, 780, 781, 782, 783, 784, 785, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795,
      796, 797, 798, 799, 800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 812, 813,
      814, 815, 816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
      29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51,
      52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74,
      75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97,
      98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116,
      117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134,
      135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152,
      153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170,
      171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188,
      189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206,
      207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224,
      225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242,
      243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260,
      261, 262, 263, 264, 265, 266, 267, 268, 269]),
   ("injectivity", [274, 276, 278, 280, 282, 284, 286, 288, 290, 292, 294, 296, 298, 300, 302, 304, 306, 308,
      310, 312, 314, 316, 318, 320, 322, 324, 326, 328, 330, 332, 334, 336, 338, 340, 342, 344,
      346, 348, 350, 352, 354, 356, 358, 360, 362, 364, 366, 368, 370, 372, 374, 376, 378, 380,
      382, 384, 386, 388, 390, 392, 394, 396, 398, 400, 402, 404, 406, 408, 410, 412, 414, 416,
      418, 420, 422, 424, 426, 428, 430, 432, 434, 436, 438, 440, 442, 444, 446, 448, 450, 452,
      454, 456, 458, 460, 462, 464, 466, 468, 470, 472, 474, 476, 478, 480, 482, 484, 486, 488,
      490, 492, 494, 496, 498, 500, 502, 504, 506, 508, 510, 512, 514, 516, 518, 520, 522, 524,
      526, 528, 530, 532]),
   ("distinctness", []),
   ("no junk", [835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847, 848, 849, 850, 851, 852,
      853, 854, 855, 856, 857, 858, 859, 860, 861, 862, 863, 864, 865, 866, 867, 868, 869, 870,
      871, 872, 873, 874, 875, 876, 877, 878, 879, 880, 881, 882, 883, 884, 885, 886, 887, 888,
      889, 890, 891, 892, 893, 894, 895, 896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906,
      907, 908, 909, 910, 911, 912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924,
      925, 926, 927, 928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942,
      943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960,
      961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975, 976, 977, 978,
      979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996,
      997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012,
      1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027,
      1028, 1029, 1030, 1031, 1032, 1033]),
   ("function functional", [560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575, 576, 577,
      578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591, 592, 593, 594, 595,
      596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607, 608, 609, 610, 611, 612, 613,
      614, 615, 616, 617, 618, 619, 620, 621, 622, 623, 624, 625, 626, 627, 628, 629, 630, 631,
      632, 633, 634, 635, 636, 637, 638, 639, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649,
      650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667,
      668, 669, 670, 671, 672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685,
      686, 687, 688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703,
      704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 720, 721,
      722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735, 736, 737, 738, 739,
      740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751, 752, 753, 754, 755, 756, 757,
      758, 759, 760, 761, 762]),
   ("hooked functional", [270, 271, 272, 533, 534, 535, 536, 537, 538, 541, 545, 553, 554, 555, 556, 557, 559, 763,
      829, 830, 831, 832, 833]),
   ("collection law", [542, 543, 544, 546, 547, 548, 549, 551, 552]),
   ("library", [1034, 1709]),
   ("set idempotence", [550]),
   ("set-variable lemma", [1710]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter functional", []),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("no direction", [539, 540, 558, 834, 1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042, 1043, 1044, 1045, 1046,
      1047, 1048, 1049, 1050, 1051, 1052, 1053, 1054, 1055, 1056, 1057, 1058, 1059, 1060, 1061,
      1062, 1063, 1064, 1065, 1066, 1067, 1068, 1069, 1070, 1071, 1072, 1073, 1074, 1075, 1076,
      1077, 1078, 1079, 1080, 1081, 1082, 1083, 1084, 1085, 1086, 1087, 1088, 1089, 1090, 1091,
      1092, 1093, 1094, 1095, 1096, 1097, 1098, 1099, 1100, 1101, 1507, 1508, 1509, 1510, 1511,
      1512, 1513, 1514, 1515, 1516, 1517, 1518, 1519, 1520, 1521, 1522, 1523, 1524, 1525, 1526,
      1527, 1528, 1529, 1530, 1531, 1532, 1533, 1534, 1535, 1536, 1537, 1538, 1539, 1540, 1541,
      1542, 1543, 1544, 1545, 1546, 1547, 1548, 1549, 1550, 1551, 1552, 1553, 1554, 1555, 1556,
      1557, 1558, 1559, 1560, 1561, 1562, 1563, 1564, 1565, 1566, 1567, 1568, 1569, 1570, 1571,
      1572, 1573, 1574, 1575, 1576, 1577, 1578, 1579, 1580, 1581, 1582, 1583, 1584, 1585, 1586,
      1587, 1588, 1589, 1590, 1591, 1592, 1593, 1594, 1595, 1596, 1597, 1598, 1599, 1600, 1601,
      1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609, 1610, 1611, 1612, 1613, 1614, 1615, 1616,
      1617, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625, 1626, 1627, 1628, 1629, 1630, 1631,
      1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1646,
      1647, 1648, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1656, 1657, 1658, 1659, 1660, 1661,
      1662, 1663, 1664, 1665, 1666, 1667, 1668, 1669, 1670, 1671, 1672, 1673, 1674, 1675, 1676,
      1677, 1678, 1679, 1680, 1681, 1682, 1683, 1684, 1685, 1686, 1687, 1688, 1689, 1690, 1691,
      1692, 1693, 1694, 1695, 1696, 1697, 1698, 1699, 1700, 1701, 1702, 1703, 1704, 1705, 1706,
      1707, 1708])]

/-- The indices of a class. -/
def classOf (n : String) : List Nat := (classes.filter (·.1 == n)).flatMap (·.2)

/-! ## Γ under every interpretation reads the same equations and rules -/

kernel_rfl fnItems_withHooks : ∀ (c : Semantics) (H : HookParams), fnItems (c.withHooks H) = fnItems c
kernel_rfl ruleItems_withHooks : ∀ (c : Semantics) (H : HookParams), ruleItems (c.withHooks H) = ruleItems c

theorem mem_Γ_fns {c : Semantics} {φ : P} (h : ΓFns c φ) : Γ c φ := Or.inl (Or.inl (Or.inr h))

/-! ## Function equations (405 sentences) -/

/-- The axioms of Γ's equations, in `fnItems`'s order. -/
noncomputable def fnAxioms (c : Semantics) : List Kore.Axiom :=
  c.allFns.flatMap fun f => (fnEquationsK c f).filterMap fun
    | .axiom a => some a
    | _ => none

theorem fnItems_eq : fnItems c = (fnAxioms c).map fun a => trAxiom [] [] ⟨0, "kernel", a⟩ := by kernel_rfl

/-- The text sentences of Γ's 405 equations, in `fnItems`'s order. -/
noncomputable def fnText : List AxiomDecl :=
  [U.ax1492, U.ax1500, U.ax1499, U.ax1498, U.ax1497, U.ax1504, U.ax1503, U.ax1506, U.ax1505,
   U.ax1502, U.ax1501, U.ax1103, U.ax1102, U.ax1491, U.ax1490, U.ax1487, U.ax1486, U.ax1489,
   U.ax1488, U.ax1165, U.ax1164, U.ax1169, U.ax1168, U.ax1167, U.ax1166, U.ax1231, U.ax1230,
   U.ax1235, U.ax1234, U.ax1233, U.ax1232, U.ax1297, U.ax1296, U.ax1301, U.ax1300, U.ax1299,
   U.ax1298, U.ax1363, U.ax1362, U.ax1367, U.ax1366, U.ax1365, U.ax1364, U.ax1429, U.ax1428,
   U.ax1433, U.ax1432, U.ax1431, U.ax1430, U.ax1459, U.ax1458, U.ax1463, U.ax1462, U.ax1461,
   U.ax1460, U.ax1465, U.ax1464, U.ax1469, U.ax1468, U.ax1467, U.ax1466, U.ax1471, U.ax1470,
   U.ax1475, U.ax1474, U.ax1473, U.ax1472, U.ax1477, U.ax1476, U.ax1481, U.ax1480, U.ax1479,
   U.ax1478, U.ax1105, U.ax1104, U.ax1109, U.ax1108, U.ax1107, U.ax1106, U.ax1111, U.ax1110,
   U.ax1115, U.ax1114, U.ax1113, U.ax1112, U.ax1117, U.ax1116, U.ax1121, U.ax1120, U.ax1119,
   U.ax1118, U.ax1123, U.ax1122, U.ax1127, U.ax1126, U.ax1125, U.ax1124, U.ax1129, U.ax1128,
   U.ax1133, U.ax1132, U.ax1131, U.ax1130, U.ax1135, U.ax1134, U.ax1139, U.ax1138, U.ax1137,
   U.ax1136, U.ax1141, U.ax1140, U.ax1145, U.ax1144, U.ax1143, U.ax1142, U.ax1147, U.ax1146,
   U.ax1151, U.ax1150, U.ax1149, U.ax1148, U.ax1153, U.ax1152, U.ax1157, U.ax1156, U.ax1155,
   U.ax1154, U.ax1159, U.ax1158, U.ax1163, U.ax1162, U.ax1161, U.ax1160, U.ax1171, U.ax1170,
   U.ax1175, U.ax1174, U.ax1173, U.ax1172, U.ax1177, U.ax1176, U.ax1181, U.ax1180, U.ax1179,
   U.ax1178, U.ax1183, U.ax1182, U.ax1187, U.ax1186, U.ax1185, U.ax1184, U.ax1189, U.ax1188,
   U.ax1193, U.ax1192, U.ax1191, U.ax1190, U.ax1195, U.ax1194, U.ax1199, U.ax1198, U.ax1197,
   U.ax1196, U.ax1201, U.ax1200, U.ax1205, U.ax1204, U.ax1203, U.ax1202, U.ax1207, U.ax1206,
   U.ax1211, U.ax1210, U.ax1209, U.ax1208, U.ax1213, U.ax1212, U.ax1217, U.ax1216, U.ax1215,
   U.ax1214, U.ax1219, U.ax1218, U.ax1223, U.ax1222, U.ax1221, U.ax1220, U.ax1225, U.ax1224,
   U.ax1229, U.ax1228, U.ax1227, U.ax1226, U.ax1237, U.ax1236, U.ax1241, U.ax1240, U.ax1239,
   U.ax1238, U.ax1243, U.ax1242, U.ax1247, U.ax1246, U.ax1245, U.ax1244, U.ax1249, U.ax1248,
   U.ax1253, U.ax1252, U.ax1251, U.ax1250, U.ax1255, U.ax1254, U.ax1259, U.ax1258, U.ax1257,
   U.ax1256, U.ax1261, U.ax1260, U.ax1265, U.ax1264, U.ax1263, U.ax1262, U.ax1267, U.ax1266,
   U.ax1271, U.ax1270, U.ax1269, U.ax1268, U.ax1273, U.ax1272, U.ax1277, U.ax1276, U.ax1275,
   U.ax1274, U.ax1279, U.ax1278, U.ax1283, U.ax1282, U.ax1281, U.ax1280, U.ax1285, U.ax1284,
   U.ax1289, U.ax1288, U.ax1287, U.ax1286, U.ax1291, U.ax1290, U.ax1295, U.ax1294, U.ax1293,
   U.ax1292, U.ax1303, U.ax1302, U.ax1307, U.ax1306, U.ax1305, U.ax1304, U.ax1309, U.ax1308,
   U.ax1313, U.ax1312, U.ax1311, U.ax1310, U.ax1315, U.ax1314, U.ax1319, U.ax1318, U.ax1317,
   U.ax1316, U.ax1321, U.ax1320, U.ax1325, U.ax1324, U.ax1323, U.ax1322, U.ax1327, U.ax1326,
   U.ax1331, U.ax1330, U.ax1329, U.ax1328, U.ax1333, U.ax1332, U.ax1337, U.ax1336, U.ax1335,
   U.ax1334, U.ax1339, U.ax1338, U.ax1343, U.ax1342, U.ax1341, U.ax1340, U.ax1345, U.ax1344,
   U.ax1349, U.ax1348, U.ax1347, U.ax1346, U.ax1351, U.ax1350, U.ax1355, U.ax1354, U.ax1353,
   U.ax1352, U.ax1357, U.ax1356, U.ax1361, U.ax1360, U.ax1359, U.ax1358, U.ax1369, U.ax1368,
   U.ax1373, U.ax1372, U.ax1371, U.ax1370, U.ax1375, U.ax1374, U.ax1379, U.ax1378, U.ax1377,
   U.ax1376, U.ax1381, U.ax1380, U.ax1385, U.ax1384, U.ax1383, U.ax1382, U.ax1387, U.ax1386,
   U.ax1391, U.ax1390, U.ax1389, U.ax1388, U.ax1393, U.ax1392, U.ax1397, U.ax1396, U.ax1395,
   U.ax1394, U.ax1399, U.ax1398, U.ax1403, U.ax1402, U.ax1401, U.ax1400, U.ax1405, U.ax1404,
   U.ax1409, U.ax1408, U.ax1407, U.ax1406, U.ax1411, U.ax1410, U.ax1415, U.ax1414, U.ax1413,
   U.ax1412, U.ax1417, U.ax1416, U.ax1421, U.ax1420, U.ax1419, U.ax1418, U.ax1423, U.ax1422,
   U.ax1427, U.ax1426, U.ax1425, U.ax1424, U.ax1435, U.ax1434, U.ax1439, U.ax1438, U.ax1437,
   U.ax1436, U.ax1441, U.ax1440, U.ax1445, U.ax1444, U.ax1443, U.ax1442, U.ax1447, U.ax1446,
   U.ax1451, U.ax1450, U.ax1449, U.ax1448, U.ax1453, U.ax1452, U.ax1457, U.ax1456, U.ax1455,
   U.ax1454, U.ax1494, U.ax1493, U.ax1496, U.ax1495, U.ax1483, U.ax1482, U.ax1485, U.ax1484]

set_option maxHeartbeats 16000000 in
/-- **Γ's equations are the text's sentences' translations, pattern for pattern** (a kernel
decision per block of 27 equations, each with the budget of the single one). -/
theorem fn_shape : (fnItems c).map (·.pat) = fnText.map (trS · |>.pat) := by
  rw [fnItems_eq, List.map_map]
  exact (by decide_map_blocks 27 15 :
    ((fnAxioms c).map fun a => (trAxiom [] [] ⟨0, "kernel", a⟩).pat) = fnText.map (trS · |>.pat))

/-- **`fnText` is the account's function-equation class**: the same indices, each once. -/
theorem fns_account : (classOf "function equation").isPerm (fnText.map (·.index)) = true := by decide +kernel

/-- **E for the equations**: Γ entails each, for every H. -/
theorem fns_entailed (H : HookParams) : ∀ ad ∈ fnText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hmem : (trS ad).pat ∈ (fnItems c).map (·.pat) := by
    rw [fn_shape]; exact List.mem_map.mpr ⟨ad, had, rfl⟩
  obtain ⟨it, hit, he⟩ := List.mem_map.mp hmem
  exact hI _ (mem_Γ_fns (Or.inl ⟨it, by rw [fnItems_withHooks]; exact hit, he⟩))

/-- **The converse for `fnItems`**: the j-th item is a consequence of `fnText[j]`. -/
theorem fns_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (fnItems (cH H))[j]? = some it →
      ∃ ad, fnText[j]? = some ad ∧ (itemsPremises [trS ad] ⊧ it.pat) := by
  intro j it hj
  rw [fnItems_withHooks] at hj
  have h1 : ((fnItems c).map (·.pat))[j]? = some it.pat := by rw [List.getElem?_map, hj]; rfl
  rw [fn_shape, List.getElem?_map] at h1
  cases hf : fnText[j]? with
  | none => rw [hf] at h1; cases h1
  | some ad =>
    rw [hf] at h1
    refine ⟨ad, rfl, fun {M} _ {I} hI => ?_⟩
    have he : (trS ad).pat = it.pat := Option.some.inj h1
    exact hI _ (Or.inl ⟨trS ad, List.mem_singleton_self _, he⟩)

/-- The priority each function sentence's attributes state is the priority of the clause whose
item is the sentence's translation, item by item in `fnItems`'s order. -/
theorem fn_prios : fnText.map (fun ad => AttrsAgree.prioOf ad.ax.attributes) =
    c.allFns.flatMap (fun f => f.clauses.map (·.prio)) := by decide +kernel

/-! ## The converse over Γ's content -/

theorem ruleItems_nil : ruleItems c = [] := by kernel_rfl

/-- The parts of Γ that are no sentence's translation: the families. -/
def Families (H : HookParams) : Premises KoreAML.Sym :=
  ΓSig (cH H) ∪ ΓCons (cH H) ∪ ΓDomains (cH H) ∪ ΓColls (cH H) ∪ ΓFallback (cH H)

/-- The function sentences as written, with definedness, and the families. -/
def Pre (H : HookParams) : Premises KoreAML.Sym :=
  (fun φ => (∃ ad ∈ fnText, (trS ad).pat = φ) ∨ ∃ x : EVar, φ = @definedness KoreAML.Sym _ x) ∪ Families H

/-- **The origin of each premise of Γ**: a function equation is the translation of a text
sentence; the text has no rule, so Γ has no rule item; everything else is one of the five parts
defined by predicates (`Families`), or definedness. -/
theorem gamma_origin (H : HookParams) : ∀ φ, Γ (cH H) φ →
    (∃ ad ∈ fnText, (trS ad).pat = φ) ∨ Families H φ ∨ (∃ x : EVar, φ = @definedness KoreAML.Sym _ x) := by
  intro φ h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h)
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr h))))
  · exact Or.inr (Or.inl (Or.inl (Or.inr h)))
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · rw [fnItems_withHooks] at hit
      have hmem : it.pat ∈ fnText.map (trS · |>.pat) := fn_shape ▸ List.mem_map.mpr ⟨it, hit, rfl⟩
      obtain ⟨ad, had, he⟩ := List.mem_map.mp hmem
      exact Or.inl ⟨ad, had, he⟩
    · exact Or.inr (Or.inr hx)
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · rw [ruleItems_withHooks, ruleItems_nil] at hit; cases hit
    · exact Or.inr (Or.inr hx)
  · exact Or.inr (Or.inl (Or.inr h))

/-- Every premise of Γ is a consequence of `Pre`. -/
theorem gamma_from (H : HookParams) : ∀ φ, Γ (cH H) φ → Pre H ⊧ φ := by
  intro φ h M _ I hI
  rcases gamma_origin H φ h with ⟨ad, had, he⟩ | hf | hx
  · exact hI _ (Or.inl (Or.inl ⟨ad, had, he⟩))
  · exact hI _ (Or.inr hf)
  · exact hI _ (Or.inl (Or.inr hx))

end KCore.TieRdrConfigDeep

#check @KCore.TieRdrConfigDeep.fn_shape
#check @KCore.TieRdrConfigDeep.fns_account
#check @KCore.TieRdrConfigDeep.fns_entailed
#check @KCore.TieRdrConfigDeep.fns_from_text
#check @KCore.TieRdrConfigDeep.fn_prios
#check @KCore.TieRdrConfigDeep.gamma_origin
#check @KCore.TieRdrConfigDeep.gamma_from
#print axioms KCore.TieRdrConfigDeep.fn_shape
#print axioms KCore.TieRdrConfigDeep.fns_account
#print axioms KCore.TieRdrConfigDeep.fns_entailed
#print axioms KCore.TieRdrConfigDeep.fns_from_text
#print axioms KCore.TieRdrConfigDeep.fn_prios
#print axioms KCore.TieRdrConfigDeep.gamma_origin
#print axioms KCore.TieRdrConfigDeep.gamma_from
