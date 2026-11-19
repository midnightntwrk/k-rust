/-
  Part Absent of the tie (C14) on `f2-examples/e2-cells-stream.kompile.kore`, test/TieE2CellsStream.lean: the sections
  `--split` puts here, in the tie's namespace. A test file imports no test file, so this one
  repeats the literals and the definitions and facts it reads. Written by
  `test/constructs/tiegen.py e2-cells-stream --split`; run from the package root:
  `lake env lean -j1 test/TieE2CellsStreamAbsent.lean`.

  Measured alone (LEAN_NUM_THREADS=1, `lake env lean -j1`, a 12G memory scope): 180 s, peak
  8.7 GiB.
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

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E2-CELLS-STREAM")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
/-- Per class of the tie (`tieClasses`), the indices (`AxiomDecl.index`) of its sentences. -/
def classes : List (String × List Nat) :=
  [("function equation", [2897, 2898, 2899, 2900, 2901, 2902, 2903, 2904, 2905, 2906, 2907, 2908, 2909, 2910, 2911,
      2912, 2913, 2914, 2915, 2916, 2917, 2918, 2919, 2920, 2921, 2922, 2923, 2924, 2925, 2926,
      2927, 2928, 2929, 2930, 2931, 2932, 2933, 2934, 2935, 2936, 2937, 2938, 2939, 2940, 2941,
      2942, 2943, 2944, 2945, 2946, 2947, 2948, 2949, 2950, 2951, 2952, 2953, 2976]),
   ("rewrite rule", [2815, 2816, 2817, 2818, 2819, 2820, 2821, 2822]),
   ("priority equation", []),
   ("constructor functional", [41, 112, 182, 251, 319, 386, 452, 517, 581, 644, 706, 767, 827, 886, 944, 1001, 1057, 1112,
      1166, 1219, 1271, 1322, 1372, 1421, 1469, 1516, 1562, 1607, 1651, 1694, 1736, 1777, 1817,
      1856, 1894, 1931, 1967, 2002, 2036, 2069, 2101, 2132, 2162, 2191, 2219, 2246, 2272, 2297,
      2321, 2344, 2366, 2387, 2407, 2426, 2444, 2461, 2477, 2492, 2506, 2519, 2531, 2542, 2552,
      2561, 2569, 2576, 2582, 2587, 2591, 2594, 2599, 2605, 2608, 2611, 2617, 2619, 2623, 2628,
      2630, 2632, 2634, 2636, 2638, 2640, 2642, 2701, 2741, 2742, 2743, 2744, 2745]),
   ("subsort", [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
      29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40]),
   ("injectivity", [2595, 2600, 2606, 2609, 2612, 2618, 2620, 2624, 2629, 2631, 2633, 2635, 2637, 2639, 2641,
      2643]),
   ("distinctness", [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64,
      65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87,
      88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108,
      109, 110, 111, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127,
      128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145,
      146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163,
      164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181,
      183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200,
      201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218,
      219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236,
      237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 252, 253, 254, 255,
      256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273,
      274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291,
      292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309,
      310, 311, 312, 313, 314, 315, 316, 317, 318, 320, 321, 322, 323, 324, 325, 326, 327, 328,
      329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346,
      347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364,
      365, 366, 367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382,
      383, 384, 385, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401,
      402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 416, 417, 418, 419,
      420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437,
      438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 453, 454, 455, 456,
      457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474,
      475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492,
      493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510,
      511, 512, 513, 514, 515, 516, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 528, 529,
      530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 544, 545, 546, 547,
      548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564, 565,
      566, 567, 568, 569, 570, 571, 572, 573, 574, 575, 576, 577, 578, 579, 580, 582, 583, 584,
      585, 586, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602,
      603, 604, 605, 606, 607, 608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620,
      621, 622, 623, 624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638,
      639, 640, 641, 642, 643, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 656, 657,
      658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671, 672, 673, 674, 675,
      676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 686, 687, 688, 689, 690, 691, 692, 693,
      694, 695, 696, 697, 698, 699, 700, 701, 702, 703, 704, 705, 707, 708, 709, 710, 711, 712,
      713, 714, 715, 716, 717, 718, 719, 720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730,
      731, 732, 733, 734, 735, 736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748,
      749, 750, 751, 752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 763, 764, 765, 766,
      768, 769, 770, 771, 772, 773, 774, 775, 776, 777, 778, 779, 780, 781, 782, 783, 784, 785,
      786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796, 797, 798, 799, 800, 801, 802, 803,
      804, 805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815, 816, 817, 818, 819, 820, 821,
      822, 823, 824, 825, 826, 828, 829, 830, 831, 832, 833, 834, 835, 836, 837, 838, 839, 840,
      841, 842, 843, 844, 845, 846, 847, 848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858,
      859, 860, 861, 862, 863, 864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876,
      877, 878, 879, 880, 881, 882, 883, 884, 885, 887, 888, 889, 890, 891, 892, 893, 894, 895,
      896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911, 912, 913,
      914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927, 928, 929, 930, 931,
      932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943, 945, 946, 947, 948, 949, 950,
      951, 952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962, 963, 964, 965, 966, 967, 968,
      969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986,
      987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1002, 1003, 1004,
      1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019,
      1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034,
      1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047, 1048, 1049,
      1050, 1051, 1052, 1053, 1054, 1055, 1056, 1058, 1059, 1060, 1061, 1062, 1063, 1064, 1065,
      1066, 1067, 1068, 1069, 1070, 1071, 1072, 1073, 1074, 1075, 1076, 1077, 1078, 1079, 1080,
      1081, 1082, 1083, 1084, 1085, 1086, 1087, 1088, 1089, 1090, 1091, 1092, 1093, 1094, 1095,
      1096, 1097, 1098, 1099, 1100, 1101, 1102, 1103, 1104, 1105, 1106, 1107, 1108, 1109, 1110,
      1111, 1113, 1114, 1115, 1116, 1117, 1118, 1119, 1120, 1121, 1122, 1123, 1124, 1125, 1126,
      1127, 1128, 1129, 1130, 1131, 1132, 1133, 1134, 1135, 1136, 1137, 1138, 1139, 1140, 1141,
      1142, 1143, 1144, 1145, 1146, 1147, 1148, 1149, 1150, 1151, 1152, 1153, 1154, 1155, 1156,
      1157, 1158, 1159, 1160, 1161, 1162, 1163, 1164, 1165, 1167, 1168, 1169, 1170, 1171, 1172,
      1173, 1174, 1175, 1176, 1177, 1178, 1179, 1180, 1181, 1182, 1183, 1184, 1185, 1186, 1187,
      1188, 1189, 1190, 1191, 1192, 1193, 1194, 1195, 1196, 1197, 1198, 1199, 1200, 1201, 1202,
      1203, 1204, 1205, 1206, 1207, 1208, 1209, 1210, 1211, 1212, 1213, 1214, 1215, 1216, 1217,
      1218, 1220, 1221, 1222, 1223, 1224, 1225, 1226, 1227, 1228, 1229, 1230, 1231, 1232, 1233,
      1234, 1235, 1236, 1237, 1238, 1239, 1240, 1241, 1242, 1243, 1244, 1245, 1246, 1247, 1248,
      1249, 1250, 1251, 1252, 1253, 1254, 1255, 1256, 1257, 1258, 1259, 1260, 1261, 1262, 1263,
      1264, 1265, 1266, 1267, 1268, 1269, 1270, 1272, 1273, 1274, 1275, 1276, 1277, 1278, 1279,
      1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287, 1288, 1289, 1290, 1291, 1292, 1293, 1294,
      1295, 1296, 1297, 1298, 1299, 1300, 1301, 1302, 1303, 1304, 1305, 1306, 1307, 1308, 1309,
      1310, 1311, 1312, 1313, 1314, 1315, 1316, 1317, 1318, 1319, 1320, 1321, 1323, 1324, 1325,
      1326, 1327, 1328, 1329, 1330, 1331, 1332, 1333, 1334, 1335, 1336, 1337, 1338, 1339, 1340,
      1341, 1342, 1343, 1344, 1345, 1346, 1347, 1348, 1349, 1350, 1351, 1352, 1353, 1354, 1355,
      1356, 1357, 1358, 1359, 1360, 1361, 1362, 1363, 1364, 1365, 1366, 1367, 1368, 1369, 1370,
      1371, 1373, 1374, 1375, 1376, 1377, 1378, 1379, 1380, 1381, 1382, 1383, 1384, 1385, 1386,
      1387, 1388, 1389, 1390, 1391, 1392, 1393, 1394, 1395, 1396, 1397, 1398, 1399, 1400, 1401,
      1402, 1403, 1404, 1405, 1406, 1407, 1408, 1409, 1410, 1411, 1412, 1413, 1414, 1415, 1416,
      1417, 1418, 1419, 1420, 1422, 1423, 1424, 1425, 1426, 1427, 1428, 1429, 1430, 1431, 1432,
      1433, 1434, 1435, 1436, 1437, 1438, 1439, 1440, 1441, 1442, 1443, 1444, 1445, 1446, 1447,
      1448, 1449, 1450, 1451, 1452, 1453, 1454, 1455, 1456, 1457, 1458, 1459, 1460, 1461, 1462,
      1463, 1464, 1465, 1466, 1467, 1468, 1470, 1471, 1472, 1473, 1474, 1475, 1476, 1477, 1478,
      1479, 1480, 1481, 1482, 1483, 1484, 1485, 1486, 1487, 1488, 1489, 1490, 1491, 1492, 1493,
      1494, 1495, 1496, 1497, 1498, 1499, 1500, 1501, 1502, 1503, 1504, 1505, 1506, 1507, 1508,
      1509, 1510, 1511, 1512, 1513, 1514, 1515, 1517, 1518, 1519, 1520, 1521, 1522, 1523, 1524,
      1525, 1526, 1527, 1528, 1529, 1530, 1531, 1532, 1533, 1534, 1535, 1536, 1537, 1538, 1539,
      1540, 1541, 1542, 1543, 1544, 1545, 1546, 1547, 1548, 1549, 1550, 1551, 1552, 1553, 1554,
      1555, 1556, 1557, 1558, 1559, 1560, 1561, 1563, 1564, 1565, 1566, 1567, 1568, 1569, 1570,
      1571, 1572, 1573, 1574, 1575, 1576, 1577, 1578, 1579, 1580, 1581, 1582, 1583, 1584, 1585,
      1586, 1587, 1588, 1589, 1590, 1591, 1592, 1593, 1594, 1595, 1596, 1597, 1598, 1599, 1600,
      1601, 1602, 1603, 1604, 1605, 1606, 1608, 1609, 1610, 1611, 1612, 1613, 1614, 1615, 1616,
      1617, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625, 1626, 1627, 1628, 1629, 1630, 1631,
      1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1646,
      1647, 1648, 1649, 1650, 1652, 1653, 1654, 1655, 1656, 1657, 1658, 1659, 1660, 1661, 1662,
      1663, 1664, 1665, 1666, 1667, 1668, 1669, 1670, 1671, 1672, 1673, 1674, 1675, 1676, 1677,
      1678, 1679, 1680, 1681, 1682, 1683, 1684, 1685, 1686, 1687, 1688, 1689, 1690, 1691, 1692,
      1693, 1695, 1696, 1697, 1698, 1699, 1700, 1701, 1702, 1703, 1704, 1705, 1706, 1707, 1708,
      1709, 1710, 1711, 1712, 1713, 1714, 1715, 1716, 1717, 1718, 1719, 1720, 1721, 1722, 1723,
      1724, 1725, 1726, 1727, 1728, 1729, 1730, 1731, 1732, 1733, 1734, 1735, 1737, 1738, 1739,
      1740, 1741, 1742, 1743, 1744, 1745, 1746, 1747, 1748, 1749, 1750, 1751, 1752, 1753, 1754,
      1755, 1756, 1757, 1758, 1759, 1760, 1761, 1762, 1763, 1764, 1765, 1766, 1767, 1768, 1769,
      1770, 1771, 1772, 1773, 1774, 1775, 1776, 1778, 1779, 1780, 1781, 1782, 1783, 1784, 1785,
      1786, 1787, 1788, 1789, 1790, 1791, 1792, 1793, 1794, 1795, 1796, 1797, 1798, 1799, 1800,
      1801, 1802, 1803, 1804, 1805, 1806, 1807, 1808, 1809, 1810, 1811, 1812, 1813, 1814, 1815,
      1816, 1818, 1819, 1820, 1821, 1822, 1823, 1824, 1825, 1826, 1827, 1828, 1829, 1830, 1831,
      1832, 1833, 1834, 1835, 1836, 1837, 1838, 1839, 1840, 1841, 1842, 1843, 1844, 1845, 1846,
      1847, 1848, 1849, 1850, 1851, 1852, 1853, 1854, 1855, 1857, 1858, 1859, 1860, 1861, 1862,
      1863, 1864, 1865, 1866, 1867, 1868, 1869, 1870, 1871, 1872, 1873, 1874, 1875, 1876, 1877,
      1878, 1879, 1880, 1881, 1882, 1883, 1884, 1885, 1886, 1887, 1888, 1889, 1890, 1891, 1892,
      1893, 1895, 1896, 1897, 1898, 1899, 1900, 1901, 1902, 1903, 1904, 1905, 1906, 1907, 1908,
      1909, 1910, 1911, 1912, 1913, 1914, 1915, 1916, 1917, 1918, 1919, 1920, 1921, 1922, 1923,
      1924, 1925, 1926, 1927, 1928, 1929, 1930, 1932, 1933, 1934, 1935, 1936, 1937, 1938, 1939,
      1940, 1941, 1942, 1943, 1944, 1945, 1946, 1947, 1948, 1949, 1950, 1951, 1952, 1953, 1954,
      1955, 1956, 1957, 1958, 1959, 1960, 1961, 1962, 1963, 1964, 1965, 1966, 1968, 1969, 1970,
      1971, 1972, 1973, 1974, 1975, 1976, 1977, 1978, 1979, 1980, 1981, 1982, 1983, 1984, 1985,
      1986, 1987, 1988, 1989, 1990, 1991, 1992, 1993, 1994, 1995, 1996, 1997, 1998, 1999, 2000,
      2001, 2003, 2004, 2005, 2006, 2007, 2008, 2009, 2010, 2011, 2012, 2013, 2014, 2015, 2016,
      2017, 2018, 2019, 2020, 2021, 2022, 2023, 2024, 2025, 2026, 2027, 2028, 2029, 2030, 2031,
      2032, 2033, 2034, 2035, 2037, 2038, 2039, 2040, 2041, 2042, 2043, 2044, 2045, 2046, 2047,
      2048, 2049, 2050, 2051, 2052, 2053, 2054, 2055, 2056, 2057, 2058, 2059, 2060, 2061, 2062,
      2063, 2064, 2065, 2066, 2067, 2068, 2070, 2071, 2072, 2073, 2074, 2075, 2076, 2077, 2078,
      2079, 2080, 2081, 2082, 2083, 2084, 2085, 2086, 2087, 2088, 2089, 2090, 2091, 2092, 2093,
      2094, 2095, 2096, 2097, 2098, 2099, 2100, 2102, 2103, 2104, 2105, 2106, 2107, 2108, 2109,
      2110, 2111, 2112, 2113, 2114, 2115, 2116, 2117, 2118, 2119, 2120, 2121, 2122, 2123, 2124,
      2125, 2126, 2127, 2128, 2129, 2130, 2131, 2133, 2134, 2135, 2136, 2137, 2138, 2139, 2140,
      2141, 2142, 2143, 2144, 2145, 2146, 2147, 2148, 2149, 2150, 2151, 2152, 2153, 2154, 2155,
      2156, 2157, 2158, 2159, 2160, 2161, 2163, 2164, 2165, 2166, 2167, 2168, 2169, 2170, 2171,
      2172, 2173, 2174, 2175, 2176, 2177, 2178, 2179, 2180, 2181, 2182, 2183, 2184, 2185, 2186,
      2187, 2188, 2189, 2190, 2192, 2193, 2194, 2195, 2196, 2197, 2198, 2199, 2200, 2201, 2202,
      2203, 2204, 2205, 2206, 2207, 2208, 2209, 2210, 2211, 2212, 2213, 2214, 2215, 2216, 2217,
      2218, 2220, 2221, 2222, 2223, 2224, 2225, 2226, 2227, 2228, 2229, 2230, 2231, 2232, 2233,
      2234, 2235, 2236, 2237, 2238, 2239, 2240, 2241, 2242, 2243, 2244, 2245, 2247, 2248, 2249,
      2250, 2251, 2252, 2253, 2254, 2255, 2256, 2257, 2258, 2259, 2260, 2261, 2262, 2263, 2264,
      2265, 2266, 2267, 2268, 2269, 2270, 2271, 2273, 2274, 2275, 2276, 2277, 2278, 2279, 2280,
      2281, 2282, 2283, 2284, 2285, 2286, 2287, 2288, 2289, 2290, 2291, 2292, 2293, 2294, 2295,
      2296, 2298, 2299, 2300, 2301, 2302, 2303, 2304, 2305, 2306, 2307, 2308, 2309, 2310, 2311,
      2312, 2313, 2314, 2315, 2316, 2317, 2318, 2319, 2320, 2322, 2323, 2324, 2325, 2326, 2327,
      2328, 2329, 2330, 2331, 2332, 2333, 2334, 2335, 2336, 2337, 2338, 2339, 2340, 2341, 2342,
      2343, 2345, 2346, 2347, 2348, 2349, 2350, 2351, 2352, 2353, 2354, 2355, 2356, 2357, 2358,
      2359, 2360, 2361, 2362, 2363, 2364, 2365, 2367, 2368, 2369, 2370, 2371, 2372, 2373, 2374,
      2375, 2376, 2377, 2378, 2379, 2380, 2381, 2382, 2383, 2384, 2385, 2386, 2388, 2389, 2390,
      2391, 2392, 2393, 2394, 2395, 2396, 2397, 2398, 2399, 2400, 2401, 2402, 2403, 2404, 2405,
      2406, 2408, 2409, 2410, 2411, 2412, 2413, 2414, 2415, 2416, 2417, 2418, 2419, 2420, 2421,
      2422, 2423, 2424, 2425, 2427, 2428, 2429, 2430, 2431, 2432, 2433, 2434, 2435, 2436, 2437,
      2438, 2439, 2440, 2441, 2442, 2443, 2445, 2446, 2447, 2448, 2449, 2450, 2451, 2452, 2453,
      2454, 2455, 2456, 2457, 2458, 2459, 2460, 2462, 2463, 2464, 2465, 2466, 2467, 2468, 2469,
      2470, 2471, 2472, 2473, 2474, 2475, 2476, 2478, 2479, 2480, 2481, 2482, 2483, 2484, 2485,
      2486, 2487, 2488, 2489, 2490, 2491, 2493, 2494, 2495, 2496, 2497, 2498, 2499, 2500, 2501,
      2502, 2503, 2504, 2505, 2507, 2508, 2509, 2510, 2511, 2512, 2513, 2514, 2515, 2516, 2517,
      2518, 2520, 2521, 2522, 2523, 2524, 2525, 2526, 2527, 2528, 2529, 2530, 2532, 2533, 2534,
      2535, 2536, 2537, 2538, 2539, 2540, 2541, 2543, 2544, 2545, 2546, 2547, 2548, 2549, 2550,
      2551, 2553, 2554, 2555, 2556, 2557, 2558, 2559, 2560, 2562, 2563, 2564, 2565, 2566, 2567,
      2568, 2570, 2571, 2572, 2573, 2574, 2575, 2577, 2578, 2579, 2580, 2581, 2583, 2584, 2585,
      2586, 2588, 2589, 2590, 2592, 2593, 2596, 2597, 2598, 2601, 2602, 2607, 2610]),
   ("no junk", [2757, 2758, 2759, 2760, 2761, 2762, 2763, 2764, 2765, 2766, 2767, 2768, 2769, 2770, 2771,
      2772, 2773, 2774, 2775, 2776, 2777, 2778, 2779, 2780, 2781]),
   ("function functional", [2707, 2708, 2709, 2710, 2711, 2712, 2713, 2714, 2715, 2716, 2717, 2718, 2719, 2720, 2721,
      2722, 2723, 2724, 2725, 2726, 2727, 2728, 2729, 2730, 2731, 2732, 2733, 2734, 2735]),
   ("hooked functional", [2625, 2626, 2627, 2644, 2646, 2647, 2648, 2649, 2650, 2651, 2652, 2654, 2655, 2656, 2657,
      2659, 2661, 2662, 2663, 2664, 2665, 2666, 2667, 2668, 2669, 2670, 2671, 2672, 2673, 2674,
      2675, 2676, 2680, 2688, 2689, 2690, 2691, 2692, 2693, 2694, 2695, 2696, 2698, 2700, 2702,
      2703, 2704, 2706, 2737, 2738, 2739, 2740, 2746, 2747, 2748, 2749, 2750, 2751, 2752, 2753,
      2754]),
   ("collection law", [2677, 2678, 2679, 2681, 2682, 2683, 2684, 2686, 2687]),
   ("library", [2787, 2788, 2789, 2790, 2791, 2792, 2793, 2794, 2795, 2796, 2797, 2798, 2799, 2800, 2801,
      2802, 2803, 2804, 2805, 2806, 2807, 2808, 2809, 2810, 2823, 2824, 2825, 2826, 2827, 2829,
      2830, 2831, 2832, 2833, 2834, 2835, 2836, 2837, 2838, 2839, 2840, 2841, 2842, 2843, 2844,
      2845, 2846, 2847, 2848, 2849, 2850, 2851, 2852, 2853, 2854, 2855, 2856, 2857, 2858, 2859,
      2860, 2861, 2862, 2863, 2864, 2866, 2867, 2868, 2869, 2870, 2871, 2872, 2873, 2874, 2875,
      2876, 2877, 2878, 2879, 2880, 2881, 2882, 2883, 2884, 2885, 2886, 2888, 2889, 2956, 2957,
      2958, 2959, 2991, 2992, 2993, 2994, 2995, 2996, 2997, 2998, 2999]),
   ("set idempotence", [2685]),
   ("set-variable lemma", [2782, 2783, 2784, 2785, 2786, 3000]),
   ("function law", []),
   ("open generator law", []),
   ("open generator functional", []),
   ("parameter functional", [2645]),
   ("parameter lemma", []),
   ("user lemma", []),
   ("user lemma at values", []),
   ("no direction", [2603, 2604, 2613, 2614, 2615, 2616, 2621, 2622, 2653, 2658, 2660, 2697, 2699, 2705, 2736,
      2755, 2756, 2811, 2812, 2813, 2814, 2828, 2865, 2887, 2890, 2891, 2892, 2893, 2894, 2895,
      2896, 2954, 2955, 2960, 2961, 2962, 2963, 2964, 2965, 2966, 2967, 2968, 2969, 2970, 2971,
      2972, 2973, 2974, 2975, 2977, 2978, 2979, 2980, 2981, 2982, 2983, 2984, 2985, 2986, 2987,
      2988, 2989, 2990])]

/-- The indices of a class. -/
def classOf (n : String) : List Nat := (classes.filter (·.1 == n)).flatMap (·.2)

/-- The sentence is in the no-direction class exactly where it applies a head Γ lacks. -/
noncomputable def absentP (ad : AxiomDecl) : Bool :=
  (classOf "no direction").contains ad.index != (appHeadsOf ad.ax.pattern).all (gammaHasHead c)

/-- The heads at which Γ applies its symbols (`gammaHeads c`), written out. -/
def gHeads : List (String × List Kore.KSort) :=
  [("kseq", []), ("dotk", []), ("Lbl'Hash'EOF", []), ("Lbl'Hash'unknownIOError", []),
   ("Lbl'Hash'E2BIG", []), ("Lbl'Hash'EACCES", []), ("Lbl'Hash'EAGAIN", []),
   ("Lbl'Hash'EBADF", []), ("Lbl'Hash'EBUSY", []), ("Lbl'Hash'ECHILD", []),
   ("Lbl'Hash'EDEADLK", []), ("Lbl'Hash'EDOM", []), ("Lbl'Hash'EEXIST", []),
   ("Lbl'Hash'EFAULT", []), ("Lbl'Hash'EFBIG", []), ("Lbl'Hash'EINTR", []),
   ("Lbl'Hash'EINVAL", []), ("Lbl'Hash'EIO", []), ("Lbl'Hash'EISDIR", []), ("Lbl'Hash'EMFILE", []),
   ("Lbl'Hash'EMLINK", []), ("Lbl'Hash'ENAMETOOLONG", []), ("Lbl'Hash'ENFILE", []),
   ("Lbl'Hash'ENODEV", []), ("Lbl'Hash'ENOENT", []), ("Lbl'Hash'ENOEXEC", []),
   ("Lbl'Hash'ENOLCK", []), ("Lbl'Hash'ENOMEM", []), ("Lbl'Hash'ENOSPC", []),
   ("Lbl'Hash'ENOSYS", []), ("Lbl'Hash'ENOTDIR", []), ("Lbl'Hash'ENOTEMPTY", []),
   ("Lbl'Hash'ENOTTY", []), ("Lbl'Hash'ENXIO", []), ("Lbl'Hash'EPERM", []), ("Lbl'Hash'EPIPE", []),
   ("Lbl'Hash'ERANGE", []), ("Lbl'Hash'EROFS", []), ("Lbl'Hash'ESPIPE", []),
   ("Lbl'Hash'ESRCH", []), ("Lbl'Hash'EXDEV", []), ("Lbl'Hash'EWOULDBLOCK", []),
   ("Lbl'Hash'EINPROGRESS", []), ("Lbl'Hash'EALREADY", []), ("Lbl'Hash'ENOTSOCK", []),
   ("Lbl'Hash'EDESTADDRREQ", []), ("Lbl'Hash'EMSGSIZE", []), ("Lbl'Hash'EPROTOTYPE", []),
   ("Lbl'Hash'ENOPROTOOPT", []), ("Lbl'Hash'EPROTONOSUPPORT", []),
   ("Lbl'Hash'ESOCKTNOSUPPORT", []), ("Lbl'Hash'EOPNOTSUPP", []), ("Lbl'Hash'EPFNOSUPPORT", []),
   ("Lbl'Hash'EAFNOSUPPORT", []), ("Lbl'Hash'EADDRINUSE", []), ("Lbl'Hash'EADDRNOTAVAIL", []),
   ("Lbl'Hash'ENETDOWN", []), ("Lbl'Hash'ENETUNREACH", []), ("Lbl'Hash'ENETRESET", []),
   ("Lbl'Hash'ECONNABORTED", []), ("Lbl'Hash'ECONNRESET", []), ("Lbl'Hash'ENOBUFS", []),
   ("Lbl'Hash'EISCONN", []), ("Lbl'Hash'ENOTCONN", []), ("Lbl'Hash'ESHUTDOWN", []),
   ("Lbl'Hash'ETOOMANYREFS", []), ("Lbl'Hash'ETIMEDOUT", []), ("Lbl'Hash'ECONNREFUSED", []),
   ("Lbl'Hash'EHOSTDOWN", []), ("Lbl'Hash'EHOSTUNREACH", []), ("Lbl'Hash'ELOOP", []),
   ("Lbl'Hash'EOVERFLOW", []), ("Lbl'Hash'systemResult", []), ("Lbl'Hash'tempFile", []),
   ("Lbl'Hash'buffer'LParUndsRParUnds'K-IO'Unds'Stream'Unds'K", []),
   ("Lbl'Hash'istream'LParUndsRParUnds'K-IO'Unds'Stream'Unds'Int", []),
   ("Lbl'Hash'parseInput'LParUndsCommUndsRParUnds'K-IO'Unds'Stream'Unds'String'Unds'String", []),
   ("Lbl'Hash'ostream'LParUndsRParUnds'K-IO'Unds'Stream'Unds'Int", []),
   ("Lbl'-LT-'generatedTop'-GT-'", []), ("Lbl'-LT-'generatedTop'-GT-'-fragment", []),
   ("Lbl'-LT-'t'-GT-'", []), ("LblnoTCell", []), ("Lbl'-LT-'t'-GT-'-fragment", []),
   ("Lbl'-LT-'k'-GT-'", []), ("LblnoKCell", []), ("Lbl'-LT-'in'-GT-'", []), ("LblnoInCell", []),
   ("Lbl'-LT-'out'-GT-'", []), ("LblnoOutCell", []), ("Lbl'-LT-'generatedCounter'-GT-'", []),
   ("LblnoGeneratedCounterCell", []), ("Lbl'Hash'noParse", []), ("Lbla", []),
   ("Lblproject'Coln'Int", []), ("append", []), ("LblisK", []), ("LblisKItem", []),
   ("LblisKConfigVar", []), ("LblisMap", []), ("LblisSet", []), ("LblisList", []),
   ("LblisBool", []), ("LblisInt", []), ("LblisFloat", []), ("LblisString", []),
   ("LblisIOError", []), ("LblisIOFile", []), ("LblisIOInt", []), ("LblisIOString", []),
   ("LblisStream", []), ("LblisGeneratedTopCell", []), ("LblisGeneratedTopCellFragment", []),
   ("LblisTCell", []), ("LblisTCellOpt", []), ("LblisTCellFragment", []), ("LblisKCell", []),
   ("LblisKCellOpt", []), ("LblisInCell", []), ("LblisInCellOpt", []), ("LblisOutCell", []),
   ("LblisOutCellOpt", []), ("LblisGeneratedCounterCell", []),
   ("LblisGeneratedCounterCellOpt", []), ("LblisExp", []),
   ("LblFloat2String'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'Float", []),
   ("Lbl'Hash'getc'LParUndsRParUnds'K-IO'Unds'IOInt'Unds'Int", []),
   ("Lbl'Hash'write'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'String", []),
   ("Lbl'Hash'argv'LParRParUnds'K-REFLECTION'Unds'List", []),
   ("Lbl'Hash'configuration'Unds'K-REFLECTION'Unds'K", []),
   ("Lbl'Hash'fresh'LParUndsRParUnds'K-REFLECTION'Unds'KItem'Unds'String", []),
   ("Lbl'Hash'getenv'LParUndsRParUnds'K-REFLECTION'Unds'K'Unds'String", []),
   ("Lbl'Hash'kompiledDirectory'LParRParUnds'K-REFLECTION'Unds'String", []),
   ("Lbl'Hash'sort'LParUndsRParUnds'K-REFLECTION'Unds'String'Unds'K", []),
   ("Lblgetsymbol'LParUndsRParUnds'K-REFLECTION'Unds'KItem'Unds'K", []), ("LblnotBool'Unds'", []),
   ("Lbl'Unds'andBool'Unds'", []), ("Lbl'Unds'andThenBool'Unds'", []),
   ("Lbl'Unds'orBool'Unds'", []), ("Lbl'Unds'orElseBool'Unds'", []),
   ("Lbl'Unds'xorBool'Unds'", []), ("Lbl'Unds'impliesBool'Unds'", []),
   ("Lbl'UndsEqlsEqls'Bool'Unds'", []), ("Lbl'UndsEqlsSlshEqls'Bool'Unds'", []),
   ("Lbl'UndsPlus'Int'Unds'", []), ("Lbl'Unds'-Int'Unds'", []), ("Lbl'UndsStar'Int'Unds'", []),
   ("Lbl'UndsSlsh'Int'Unds'", []), ("Lbl'UndsPerc'Int'Unds'", []), ("Lbl'Unds'divInt'Unds'", []),
   ("Lbl'Unds'modInt'Unds'", []),
   ("LblminInt'LParUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int", []),
   ("LblmaxInt'LParUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int", []),
   ("Lbl'Unds-LT-'Int'Unds'", []), ("Lbl'Unds-LT-Eqls'Int'Unds'", []),
   ("Lbl'Unds-GT-'Int'Unds'", []), ("Lbl'Unds-GT-Eqls'Int'Unds'", []),
   ("Lbl'UndsEqlsEqls'Int'Unds'", []), ("Lbl'UndsEqlsSlshEqls'Int'Unds'", []),
   ("LblabsInt'LParUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int", []),
   ("LblfreshInt'LParUndsRParUnds'INT'Unds'Int'Unds'Int", []), ("Lbl'Unds-GT--GT-'Int'Unds'", []),
   ("Lbl'Unds-LT--LT-'Int'Unds'", []),
   ("Lbllog2Int'LParUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int", []),
   ("Lbl'UndsXor-Perc'Int'UndsUnds'", []),
   ("LblbitRangeInt'LParUndsCommUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int'Unds'Int", []),
   ("LblsignExtendBitRangeInt'LParUndsCommUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int'Unds'Int", []),
   ("Lbl'UndsXor-'Int'Unds'", []), ("Lbl'UndsEqlsEqls'K'Unds'", []),
   ("Lbl'UndsEqlsSlshEqls'K'Unds'", []), ("Lbl'Stop'Map", []), ("Lbl'UndsPipe'-'-GT-Unds'", []),
   ("Lbl'Unds'Map'Unds'", []), ("LblMap'Coln'update", []),
   ("Lbl'UndsLSqBUnds-LT-'-undef'RSqB'", []), ("LblMap'Coln'lookup", []),
   ("LblMap'Coln'lookupOrDefault", []),
   ("Lbl'Unds'in'Unds'keys'LParUndsRParUnds'MAP'Unds'Bool'Unds'KItem'Unds'Map", []),
   ("LblsizeMap", []),
   ("LblremoveAll'LParUndsCommUndsRParUnds'MAP'Unds'Map'Unds'Map'Unds'Set", []),
   ("Lblkeys'LParUndsRParUnds'MAP'Unds'Set'Unds'Map", []), ("Lbl'Stop'Set", []),
   ("LblSetItem", []), ("Lbl'Unds'Set'Unds'", []),
   ("Lbl'UndsPipe'Set'UndsUnds'SET'Unds'Set'Unds'Set'Unds'Set", []),
   ("LblintersectSet'LParUndsCommUndsRParUnds'SET'Unds'Set'Unds'Set'Unds'Set", []),
   ("LblSet'Coln'difference", []), ("LblSet'Coln'in", []),
   ("Lbl'Unds-LT-Eqls'Set'UndsUnds'SET'Unds'Bool'Unds'Set'Unds'Set", []),
   ("Lblsize'LParUndsRParUnds'SET'Unds'Int'Unds'Set", []), ("Lbl'Unds'List'Unds'", []),
   ("Lbl'Stop'List", []), ("LblListItem", []), ("LblpushList", []), ("LblList'Coln'get", []),
   ("LblList'Coln'range", []), ("Lbl'Unds'inList'Unds'", []), ("LblsizeList", []),
   ("LblList'Coln'set", []),
   ("LblmakeList'LParUndsCommUndsRParUnds'LIST'Unds'List'Unds'Int'Unds'KItem", []),
   ("LblupdateList'LParUndsCommUndsCommUndsRParUnds'LIST'Unds'List'Unds'List'Unds'Int'Unds'List", []),
   ("LblfillList'LParUndsCommUndsCommUndsCommUndsRParUnds'LIST'Unds'List'Unds'List'Unds'Int'Unds'Int'Unds'KItem", []),
   ("Lbl'UndsPlus'Float'UndsUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float", []),
   ("Lbl'Unds'-Float'UndsUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float", []),
   ("Lbl'UndsStar'Float'UndsUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float", []),
   ("Lbl'UndsSlsh'Float'UndsUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float", []),
   ("Lbl'UndsPerc'Float'UndsUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float", []),
   ("Lbl--Float'UndsUnds'FLOAT'Unds'Float'Unds'Float", []),
   ("LblabsFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float", []),
   ("LblfloorFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float", []),
   ("LblceilFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float", []),
   ("LbltruncFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float", []),
   ("LblsqrtFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float", []),
   ("Lbl'Unds-LT-Eqls'Float'UndsUnds'FLOAT'Unds'Bool'Unds'Float'Unds'Float", []),
   ("Lbl'Unds-LT-'Float'UndsUnds'FLOAT'Unds'Bool'Unds'Float'Unds'Float", []),
   ("Lbl'Unds-GT-Eqls'Float'UndsUnds'FLOAT'Unds'Bool'Unds'Float'Unds'Float", []),
   ("Lbl'Unds-GT-'Float'UndsUnds'FLOAT'Unds'Bool'Unds'Float'Unds'Float", []),
   ("Lbl'UndsEqlsEqls'Float'Unds'", []),
   ("Lbl'UndsEqlsSlshEqls'Float'UndsUnds'FLOAT'Unds'Bool'Unds'Float'Unds'Float", []),
   ("LblisNaN'LParUndsRParUnds'FLOAT'Unds'Bool'Unds'Float", []),
   ("LblisInfinite'LParUndsRParUnds'FLOAT'Unds'Bool'Unds'Float", []),
   ("LblprecisionFloat'LParUndsRParUnds'FLOAT'Unds'Int'Unds'Float", []),
   ("LblexponentBitsFloat'LParUndsRParUnds'FLOAT'Unds'Int'Unds'Float", []),
   ("LblroundFloat'LParUndsCommUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Float'Unds'Int'Unds'Int", []),
   ("LblInt2Float'LParUndsCommUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Int'Unds'Int'Unds'Int", []),
   ("LblmaxValueFloat'LParUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Int'Unds'Int", []),
   ("LblminValueFloat'LParUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Int'Unds'Int", []),
   ("Lbl'UndsPlus'String'UndsUnds'STRING-COMMON'Unds'String'Unds'String'Unds'String", []),
   ("LbllengthString'LParUndsRParUnds'STRING-COMMON'Unds'Int'Unds'String", []),
   ("LblordChar'LParUndsRParUnds'STRING-COMMON'Unds'Int'Unds'String", []),
   ("LblsubstrString'LParUndsCommUndsCommUndsRParUnds'STRING-COMMON'Unds'String'Unds'String'Unds'Int'Unds'Int", []),
   ("LblfindString'LParUndsCommUndsCommUndsRParUnds'STRING-COMMON'Unds'Int'Unds'String'Unds'String'Unds'Int", []),
   ("LblrfindString'LParUndsCommUndsCommUndsRParUnds'STRING-COMMON'Unds'Int'Unds'String'Unds'String'Unds'Int", []),
   ("LblfindChar'LParUndsCommUndsCommUndsRParUnds'STRING-COMMON'Unds'Int'Unds'String'Unds'String'Unds'Int", []),
   ("LblrfindChar'LParUndsCommUndsCommUndsRParUnds'STRING-COMMON'Unds'Int'Unds'String'Unds'String'Unds'Int", []),
   ("LblString2Bool'LParUndsRParUnds'STRING-COMMON'Unds'Bool'Unds'String", []),
   ("LblString2Int'LParUndsRParUnds'STRING-COMMON'Unds'Int'Unds'String", []),
   ("LblString2Base'LParUndsCommUndsRParUnds'STRING-COMMON'Unds'Int'Unds'String'Unds'Int", []),
   ("Lblreplace'LParUndsCommUndsCommUndsCommUndsRParUnds'STRING-COMMON'Unds'String'Unds'String'Unds'String'Unds'String'Unds'Int", []),
   ("LblreplaceFirst'LParUndsCommUndsCommUndsRParUnds'STRING-COMMON'Unds'String'Unds'String'Unds'String'Unds'String", []),
   ("LblcountAllOccurrences'LParUndsCommUndsRParUnds'STRING-COMMON'Unds'Int'Unds'String'Unds'String", []),
   ("LblreplaceAll'LParUndsCommUndsCommUndsRParUnds'STRING-COMMON'Unds'String'Unds'String'Unds'String'Unds'String", []),
   ("Lbl'UndsEqlsEqls'String'UndsUnds'STRING-COMMON'Unds'Bool'Unds'String'Unds'String", []),
   ("Lbl'UndsEqlsSlshEqls'String'UndsUnds'STRING-COMMON'Unds'Bool'Unds'String'Unds'String", []),
   ("Lbl'Unds-LT-'String'UndsUnds'STRING-COMMON'Unds'Bool'Unds'String'Unds'String", []),
   ("Lbl'Unds-LT-Eqls'String'UndsUnds'STRING-COMMON'Unds'Bool'Unds'String'Unds'String", []),
   ("Lbl'Unds-GT-'String'UndsUnds'STRING-COMMON'Unds'Bool'Unds'String'Unds'String", []),
   ("Lbl'Unds-GT-Eqls'String'UndsUnds'STRING-COMMON'Unds'Bool'Unds'String'Unds'String", []),
   ("LblchrChar'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'Int", []),
   ("LblInt2String'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'Int", []),
   ("LblBool2String'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'Bool", []),
   ("LblBytes2Int'LParUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Int'Unds'Bytes'Unds'Endianness'Unds'Signedness", []),
   ("Lbl'UndsLSqBUnds-LT-'-'UndsRSqBUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes'Unds'Int'Unds'Int", []),
   ("Lbl'UndsLSqBUndsRSqBUnds'BYTES-HOOKED'Unds'Int'Unds'Bytes'Unds'Int", []),
   ("LblsubstrBytes'LParUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes'Unds'Int'Unds'Int", []),
   ("LblreplaceAtBytes'LParUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes'Unds'Int'Unds'Bytes", []),
   ("LblmemsetBytes'LParUndsCommUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes'Unds'Int'Unds'Int'Unds'Int", []),
   ("LblpadRightBytes'LParUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes'Unds'Int'Unds'Int", []),
   ("LblpadLeftBytes'LParUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes'Unds'Int'Unds'Int", []),
   ("LblreverseBytes'LParUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes", []),
   ("LbllengthBytes'LParUndsRParUnds'BYTES-HOOKED'Unds'Int'Unds'Bytes", []),
   ("Lbl'UndsPlus'Bytes'UndsUnds'BYTES-HOOKED'Unds'Bytes'Unds'Bytes'Unds'Bytes", []),
   ("Lbl'Stop'Bytes'Unds'BYTES-HOOKED'Unds'Bytes", []),
   ("LblInt2Bytes'LParUndsCommUndsCommUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'Int'Unds'Int'Unds'Endianness", []),
   ("Lblite", []), ("Lbl'Stop'RangeMap", []), ("Lbl'Unds'r'Pipe'-'-GT-Unds'", []),
   ("Lbl'Unds'RangeMap'Unds'", []), ("LblRangeMap'Coln'lookup", []),
   ("LblRangeMap'Coln'lookupOrDefault", []), ("LblRangeMap'Coln'find'Unds'range", []),
   ("LblRangeMap'Coln'update", []), ("Lbl'Unds'r'LSqBUnds-LT-'-undef'RSqB'", []),
   ("Lbl'Unds'-RangeMap'UndsUnds'RANGEMAP'Unds'RangeMap'Unds'RangeMap'Unds'RangeMap", []),
   ("LblupdateRangeMap'LParUndsCommUndsRParUnds'RANGEMAP'Unds'RangeMap'Unds'RangeMap'Unds'RangeMap", []),
   ("LblremoveAll'LParUndsCommUndsRParUnds'RANGEMAP'Unds'RangeMap'Unds'RangeMap'Unds'Set", []),
   ("Lbl'Unds'in'Unds'keys'LParUndsRParUnds'RANGEMAP'Unds'Bool'Unds'KItem'Unds'RangeMap", []),
   ("LblsizeRangeMap", []),
   ("Lbl'Unds-LT-Eqls'RangeMap'UndsUnds'RANGEMAP'Unds'Bool'Unds'RangeMap'Unds'RangeMap", []),
   ("Lblkeys'LParUndsRParUnds'RANGEMAP'Unds'Set'Unds'RangeMap", []),
   ("inj", [.ctor ⟨⟨"SortTCell"⟩⟩ [], .ctor ⟨⟨"SortTCellOpt"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortKCell"⟩⟩ [], .ctor ⟨⟨"SortKCellOpt"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortInCell"⟩⟩ [], .ctor ⟨⟨"SortInCellOpt"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortOutCell"⟩⟩ [], .ctor ⟨⟨"SortOutCellOpt"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortGeneratedCounterCell"⟩⟩ [], .ctor ⟨⟨"SortGeneratedCounterCellOpt"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortInt"⟩⟩ [], .ctor ⟨⟨"SortIOInt"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortIOError"⟩⟩ [], .ctor ⟨⟨"SortIOInt"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortString"⟩⟩ [], .ctor ⟨⟨"SortIOString"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortIOError"⟩⟩ [], .ctor ⟨⟨"SortIOString"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortIOError"⟩⟩ [], .ctor ⟨⟨"SortIOFile"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortKConfigVar"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortMap"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortSet"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortList"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortBool"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortInt"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortFloat"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortString"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortIOError"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortIOFile"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortIOInt"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortIOString"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortStream"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortGeneratedTopCell"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortGeneratedTopCellFragment"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortTCell"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortTCellOpt"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortTCellFragment"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortKCell"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortKCellOpt"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortInCell"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortInCellOpt"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortOutCell"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortOutCellOpt"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortGeneratedCounterCell"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortGeneratedCounterCellOpt"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   ("inj", [.ctor ⟨⟨"SortExp"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []])]

/-- The literal is Γ's heads. -/
theorem gHeads_eq : gammaHeads c = gHeads := by decide +kernel

/-- `absentP` with Γ's heads read from the literal `gHeads`. -/
noncomputable def absentPL (ad : AxiomDecl) : Bool :=
  (classOf "no direction").contains ad.index !=
    (appHeadsOf ad.ax.pattern).all (fun h => gHeads.any fun g => decide (g = h))

/-- `absentPL` is `absentP`: `gammaHasHead c` is membership in `gammaHeads c`, which is `gHeads`. -/
theorem absentPL_eq : absentPL = absentP := by
  funext ad; unfold absentPL absentP gammaHasHead; rw [gHeads_eq]

/-- Γ's heads (`gHeads`), each name as its code (`KoreAML.Distinct.strCode`), written out. -/
def gCodes : List (Nat × List Kore.KSort) :=
  [(6197441387, []), (6097760100, []), (100987944911744851354065855052, []),
   (35480656676607336660446062136784281716501299369247269452, []),
   (6638152083041146951584319435203148, []), (1761593450407249393583583129290695244, []),
   (1735712938534604872879331524460962380, []), (6617473242482727251961402534683212, []),
   (7004033637090019381981677963993676, []), (1683851451315270527180573478348415564, []),
   (440370465541176411775342634438134358604, []), (26407509966551881277108258628172, []),
   (1767070182873231339710779408320848460, []), (1766929149627009649118540948593992268, []),
   (6638152107219663343876902929326668, []), (6862133840094383941238563898417740, []),
   (1725167751508185279116300932686307916, []), (103766056445219269197540647500, []),
   (1756482367376723250599524148504715852, []), (1689043747566924593362560128975135308, []),
   (1720238095394250921402661413801714252, []),
   (478358105093721682025466358192925650050497089659468, []),
   (1689043747568133519182174758149841484, []), (1777170423940552544244643215790858828, []),
   (1766968451138078268285735341937943116, []), (429700701465099003445587890779783455308, []),
   (1720015227502762251104660610018468428, []), (1730440465267201723966907090723430988, []),
   (1678741078556468701642291108459078220, []), (1762000369979458808732594574988173900, []),
   (449659486129537245530215703627439039052, []),
   (30082429104731330796709452013426044643861068, []), (1793052818310812030415995410251014732, []),
   (6800418202390499333777026282447436, []), (6760560558848489405640426254000716, []),
   (6598144063634286798953936054936140, []), (1688942730118338486323476162688082508, []),
   (6881307375788178108812932831535692, []), (1689124880307442853175394380276326988, []),
   (6657964115324422224786567784587852, []), (6942071979355065738639200117088844, []),
   (1891177002891124601452725149202171657270015582796, []),
   (1937204871906430068082378048094008271281987543628, []),
   (117488142996739520683647421840715863056972, []),
   (112722933608119751714091106592393488261708, []),
   (492921807971244781941204482258304240362337522704972, []),
   (110711780495687293407849904704141004661324, []),
   (7254741569594702408917628105839234476816491084, []),
   (1942847830560950496522357096652528419772560073292, []),
   (8344659456745239518835258836718917140807189619010821710412, []),
   (8344659456745239518835284614709860603657121213526028608076, []),
   (7500048404345703576332065700500020051250537036, []),
   (497380462690904111792755843646049002689302136382028, []),
   (497380462690904111792755825512161708469864515789388, []),
   (7255001537316466809363090935803675184819102284, []),
   (124323009787508435080264278684904258057290668412002892, []),
   (113770364964559026517066036745998382686796, []),
   (1874048808645993223150499962753488141663450456652, []),
   (29641767385977996202990753082039742036206156, []),
   (473922331291173888523854110977471469075569146880588, []),
   (7588292450810246046868681136709366371798770252, []),
   (450973480609602893741873049618212479564, []), (444368757391549029012811359326506345036, []),
   (113758401892317647520656445509195856110156, []),
   (29125213430928376599124507351493420535013964, []),
   (495850230334149052562042136312029541746914385224268, []),
   (29647206581480226543416370469193493749981772, []),
   (473922309248707082439257213050142919907538151170636, []),
   (29125213430928220295896363556472793598812748, []),
   (479756495013374265127637497992351113763050947895884, []),
   (6821173193186296558891657924993612, []), (29906497768037629531705354645919626408256076, []),
   (544297799329924054248500163978062364261933692772940, []),
   (121624908234166031500913646392706566218316, []),
   (940217292413193788758609120427639321524088727387568649454246789674521362850243133329124426018243001612508612711220571109788034330813004, []),
   (17740407130094678063673089884256875218968734827569625186374314336698578890403298115853935130792797861338211864301846600551345529398030207050316, []),
   (7043247918906501349609977254987418258284403222913236261584024226074019212951456112950231830002848740549290028943157877623631804657821972679477831310645694259341900954737786685969641133385989025214227046988, []),
   (17740407130094678063673089884256875218968734827569625186374314336698578890403298115853935130792797861338211864301846600579679728295248078332492, []),
   (121428802336216206740958059929080174872702535030001388262469165644, []),
   (723510575035956901380327913738874742029515191727491810128586290066398996996788868375116, []),
   (392357621476765017069117385598760149580, []), (1720940944893170330395212, []),
   (2337788752526703604478181265127678412558030166387131780194892, []),
   (392357621476764974567819039771953226316, []), (1720940944883274725745228, []),
   (100443551098051837427701832470203684643404, []), (440560881899928176862978636, []),
   (25713549081101272253248734774160019719742028, []), (112783585766826308560082461260, []),
   (521532734826497016649662551218561087122972325775062832838783014564719780428, []),
   (2287522883088336244638867367476247085107051579558290160116300, []),
   (475133828538666563716956634395167187532, []), (5929460300, []),
   (8305484458331914469687225591893442926933205580, []), (391900287758433, []),
   (364434038743628, []), (1725535266710405929263692, []),
   (1923124077015793602518953244536627788, []), (26544582836783702604, []),
   (26833945709912023628, []), (6870505057665443193420, []), (6722644552554359054924, []),
   (26836467989586141772, []), (1758517694672355044647500, []), (434525774710203846973219404, []),
   (114644184857577062080820568652, []), (432098475157049142409978444, []),
   (1758754755997264037831244, []), (28477081171407909146983557521996, []),
   (441717865076638021795471948, []), (532605425241745453507524652420459454565755214651980, []),
   (10040726237058829336038956037158422865491579578865221826606303537816140, []),
   (1720940944893187426378316, []), (29507634793561199066758578463308, []),
   (32443336247060855527692384442150408768217676, []), (1720940944883291821728332, []),
   (29507634793561199056862973813324, []), (440560881899928193958961740, []),
   (7553954507151666968362408892719692, []), (112783585766826308577178444364, []),
   (1933812353830826744345467600220480076, []),
   (2287522883088336244638867367476247085107051579558307256099404, []),
   (39222374256998602510383582347347576723698573932127104238925854302796, []),
   (26551047965155025484, []),
   (21443945562685259940194543208518850716462490460939958132739723711410377081191151440964616275978309693455963273457051434131222889171775000262253085094578444401598292556, []),
   (4130510410781641971243815729521988181738656212745178011287107779531892825192819003144346965421172215062035183656558876492270549099084, []),
   (347258933062786887722310869030994229251303541599800737262844346000669764602069786112031990583902778691737816437351781070456965832906708925424134536603916061232688800568468044, []),
   (14675309732705565074030913594148748258265031306738635961886173605751331772666767873879749774664786415612627280284377676, []),
   (199098756063051462948973938692521731521651768503685755770955283472986575195698672980314793475122103330578163851852, []),
   (315830159763924609908200062846761691851585118060393371986311575226853889520466453359098277542255333139413589918583198419797314321740407678778429249749572985315916, []),
   (18824944482083595389616493156336660539992304479654391158405958599866038147692944645984353606309470615050933319386131119793351767109244874459637186963464780, []),
   (18824944482083595389616493156338746573606368140482687792784104768287650040161115619126368525447178176539785339878838848075687585034228539373981834123436620, []),
   (264647640484959763865389019903819785952308859363168064219495420523764233297173923818509680847163467489330021194853165396005082466155004246208488956492, []),
   (4038202522048336241631241153121702865337799034346799214194363825607522301590310779484975063667576030791988932140490780728847279156662278673949260, []),
   (392721409877693815432988761667004031564, []),
   (110541249699099855892391312445803995868708249499624012, []),
   (474771052316603721696133595434940758308856902371353117286228556, []),
   (431801756637108812079653581170041260959453743440460, []),
   (1854574423111733287875521810721331632085176143320548117340748, []),
   (110541249699099855892391316779911673616259842661179980, []),
   (474771052316603721696133602081102924831589231873303763678421580, []),
   (121541389393050552754210176289927329604225962435654588342054183500, []),
   (522016292553553413754055433475632494852177869876792572698254621020567396940, []),
   (110541249699099866520250115792059833262706237461258828, []),
   (6588771921342603356853161313397830312182702668, []),
   (110541249699099866520250115458434141321163763532718668, []),
   (110541249699099866520250112385306928928913444267909708, []),
   (110541249699099866520250110836639842096961162824147532, []),
   (431801756637108853594751451957700876051267474711116, []),
   (431801756637108853594745888523580307873632283812428, []),
   (359818203948122867293303604482612618905088028486620872813118667338780911453577053668790488270385212089664343204673559946156014899634221156181428150549519669368113776173015628, []),
   (359818203948122867293303604482612618905088028486620872813118667338780911453577053668790488270385212089664343204673559946156014899634221156181428150549519669368124736929555020, []),
   (110541249699099866520250094088062832357774255480136268, []),
   (474771052316603767342439569020479967466498625674917660236472908, []),
   (110541249699099866520250094088039220525359907254067788, []),
   (474771052316603767342439569020479967466475013842503312010404428, []),
   (474771052316603767342439569020479989159638703121547517066240588, []),
   (2039126142787318218526170781799296293077820574614511115498546619212390988, []),
   (4130510410781641971243815729516411916268814686839138853190129920375841703014865331853643666213555791693836718933537081955189229642316, []),
   (3756677334223824774420623479742436680925324881010150535360749296241214041619179286744396004826574683887559779081744310860, []),
   (474771052316603767342439475849051375238274334989369150876181068, []),
   (474771052316603767342439475849152787286316205173903235358679628, []),
   (1057410665160100344638416826756201450564816559830819546416673259616215475971805524954532778550670282673622200046985492962238126990582348, []),
   (2039126142787794885943691446649778161763015347094001243221605056999350860, []),
   (34463737067054453708261914389949095460273400893812449602330655995567421060377131071393750659243889322969411998734251810620725311657644544534412489999194821798760707264100949770510837028613207476711485456178392284861963057259084, []),
   (41664101580771881637672447403171598916658895240499230309182649367834624854943476625330656820841565728441732337184554044091862969257728010814078548034046866468247489739193380207944483526190065909085766908236816448398177741472407404255045717995931066956, []),
   (110541249699099866520250094124496682983108737814520396, []),
   (7244431340280205256563526134932324411981019876294319170124, []),
   (31114595684620929053107634095961031260542442552826855547696524845644, []),
   (114008113768501626313175229004, []),
   (7244431340280339855840920836210215346772346621796345995852, []),
   (25737390317744543109070370697722766016930380, []),
   (31138688288827425678961365311950143168995916, []),
   (34188719201792904902010916185151803341388823883782707842803890857426458164093516, []),
   (32097277065817937160513244483529207498695244, []),
   (153206209948795800229742253919078430887182629684412494733283975756, []),
   (355904663881745816747611301990166375698979510387134345344343749986365654080402482007456946952727689470058293365614080633607305563860212109481691584624919825328583544178238028, []),
   (1739625776869486160011852, []),
   (83768830100704611514832748496617513954056810367044455537429299529696898644046902876611646871845298876649924574360283009562196900526747541308807922060571730735030860, []),
   (865156312811772925346444298571725572173587415257557439995249195936431637760265223408137719226262694676963025484, []),
   (115250917845264362322644460108, []), (1725535266755425407361612, []),
   (25737390317744544351874447460458775486161484, []),
   (1057311282280751701680793791927645271583425324347419432914207084811285018187939049314840122085741484993525676331988496407321326394303052, []),
   (1405407756666823019580439434632103007478270112683483554017731168962547490693617006363443128355357986672756190615174023281948131704666513270370743972906185632929622616990284, []),
   (133714876552366999791601052533520075769802662930571852, []),
   (7431693075409800328385312185934412, []),
   (1162526049046439129347931537318160701373401574240627691793327617662387934523617425196667985861987969948166201381799712974285593555322550745305997900, []),
   (874587394136219348471392225015801214673787687036255140038605470909367223159335324207963408161392285885162873420, []),
   (6588771921342603358439418382093192748398830156, []), (29508594528274225342887907582540, []),
   (441737028289404391400432204, []), (450265419456077294388142668, []),
   (494999328626962676979381452409257353804, []),
   (31134281882478915100800596151513682761507404, []),
   (431801756637108853698685808874244120968604796346956, []), (450265419455240514550129228, []),
   (494999572015877920799426539776272785996, []),
   (1378991927647055423374985896269032264775223336800339596596997216873938562780913148762825711625103197086527165603217442539902841634848728502664237563438460518378328558428748, []),
   (8024645462318859050392881966990660357767370346998469150762286569333359179493691609626750401997287840900010690862031575574599564214682119451309734732514649156696743344477638210712686056928724793712138991966974693368396, []),
   (2678924720470327893023682407866081270739668438286102840877359916391689023491043433377163414732100944543106312628500490569110169870961588469467488189012718276681604589733144837901202543083006968626732066118646377981270550458606654528858024630856793635709516, []),
   (1278158757846668955099257422144909981145900669517271225144376611645358319477970077858247181723332281492142092861428696163689090037556957865412625350625061528140, []),
   (76184198728005227750495518573815225431078712315396739551089800098261733023999338022365998132427470772990113071288388738852089049697447033206966011585100, []),
   (1278158757846668955099257422144909981145900669517271225144376611645358319477970077858247181723332281492142092861428696163689090037556624239720683808151132987980, []),
   (1278158757846668955099257422144909981145900669517271225144376611645358319477970077858247181723332281492142092861428696163689090037553551112508291557831868179020, []),
   (1278158757846668955099257422144909981145900669517271225144376611645358319477970077858247181723332281492142092861428696163689090037552002445421459605550424416844, []),
   (223885238066731617274542746151453078888082066993629414087115869494980692679650728461091877236286967684524394963532, []),
   (1057268144255624594408875507514855926914347676806537327832554850237804243434800670817832831487709743258313437446528910093646811603165772, []),
   (69289125101936613419180065260493598026258689347193230316834314665184738897743096762717492444378545734176829436495718651897169062198963364428, []),
   (270660644929439896168672129923803117290073005262473555925134041660877886319308971729365204860853694274128239986311400983971621159184392780, []),
   (69289125101936613419180065260493598026258689347193230316834314665184738897743096762717492444378545734176829436495718651896087923436492186188, []),
   (270660644929439896168672129923803117290073005262473555925134041660877886319308971729365204860853694274128239986311400983973882906410771020, []),
   (21443945562685259940194543210928338054240703047035875070054900476153868762879466028686577059614369870658392253138452620204192556828837903755133119025538586977814471244, []),
   (4992807647838550605856474305253554613851174490301840722108003794251444927155847202215012409634508628085812612701778444509066770955842588235772305959486775884, []),
   (21443945562685259940194543210928338054240703047035875070054900476153868762879466028686577059614369870658392253138452620204192556828837903755133095413706172629588402764, []),
   (4992807647838550605856474305253554613851174490301840722108003794251444927155847202215012409634508628085812612701778444509066770955842564623939891611260707404, []),
   (31114595684620944477773074767204953812994952830104929799984361792076, []),
   (92101044888937509384394478968596041742596093699066633164627506469615694200443285383151846305227560966125544715169407363822515873666480266392078403342875413693054687401474810444, []),
   (246164422541769359821657535490106244337092768812147572204751573734553143573700865198361862257942873870445342474855810488623692, []),
   (270660644929439896168672129905143206654258852292163223077172895998576214226697672118750400299909468034512817670727074940791940450259591756, []),
   (4540932102680517897039384756913686315119381720433514137833175150655572754422741862237528618774727604144335608364764425477283546851096599945044556, []),
   (76184198728005227750495518573848408665001932910164680329480951468381085704665295535001260943365260355892013678027059581411170348044012501572579886916172, []),
   (525874894211646327335539465178666617740988172815004807542197659684655805545500813258062929485749857376600460735893807354050688610506159636946046706392981026476727214222179737569810980270095677563931929441860735855382782540, []),
   (31344586265781302889319626401583350762187729645859189624689548505163999791233081529618725700930054264776811976508313417907481000454955612797240225215425049715457255408958549614373425198225300647987292151896855044684, []),
   (1545407418462645795614487021051740198834264410341812772287597428945449495164986181895779889665482646909867941944229663571760569292689550530219717978644956240952043741618521239460799052, []),
   (1545407418462645795614487021051740198834264410341812772287597428945449495164986181895779889665482646909867941944229663571760569292689550530219717978644956240952043741618510278704259660, []),
   (97744700096415190049420025006180177383269303311070178874375791931710490110710108590110618807452697315279101908165710795667685449632912627701998900843808412499597187397931462830420776477260, []),
   (315830159763924609908200062846839709210420134331616959945285715341710654491762327489756176525104137857053636274003949593085632018113046676778737094595730727526988, []),
   (287245856965386892541755571843932292913832620189729786893881933194016396093286246004714645573680298054617775300361199327276728649817002408472128283212, []),
   (41664101580771881637672447403171598916658895175287767545764719303340507588494951948594266665138409099753343749175251417307002354088789689031074735404176063559237732627672131136085032222707419020792286665551955231441212062725770565799139914756788085324, []),
   (635743737499570947840456229412010895536708534729752849735059589881431508606639103938840407501241113629831330509169214861349486263364385470240383653539880954425538962158997147703866720097397873599577836673490000698180322803143026080710399298921036, []),
   (162750396799890162647156794729474789257397384890816729532175255009646466203299610608343144320317725089236820610347319004505468483421282680381538215306209524332937974312703269812189880344933855641491926188413440178734162637604614676661862220625109580, []),
   (9700679588311324277350711508361982658946358256984754176865533292868522775369859374066778678912980859830189979693133771688071994985418479465337885338438124914940474886459307063352458497579923608391995798850860606356524510012731705714065302092, []),
   (2483373974607699015001782146140667560690267713788097069277576522974341830494683999761095341801723100116528634801442245552146430716267130743126498646640159978224761570933582608218229375380460443748350924505820315227270274563259316662800818659916, []),
   (315830159763924609908200062846751033551577114365542258520898468071364865534941957284073733604562865385773205920799463933599909706481627148139049036298236900172364, []),
   (4819185787413400419741822248029170367590639256769057616352626271693582984798619499050234627153078275406702213653624719132776368493810283110075344648902828620, []),
   (111358340382783548567571311323574351269602588539835479811656358589787696727424310411795614862108655361593036302583181018173201028066871339457126184697122357553211603968330535378825337610184060088115788, []),
   (929140513278490685034793801323958888658952632714447772656861063235971372053944493545120310243182938166663128127257159445026367299431066027292754951500640062433713417112591924111635241663095100524197974552972612069709652759921278501882890859047167944829158871607476118159077451331514861812998732, []),
   (11318063036038816616853562875845436906649041088530840937320202021670123186222903423159217928070420622786993286898071687376218397459565238167244120376670738584320823388113088060051496766424182974688369721250721066056016027722245921151967446445257615874292265945686604, []),
   (33260797902785442906837272006560232390804317436275313278985696640800038241167547777640894630873406015366207412622579875164156845329222149641346480609132954052847621276002931319217580617685957580881463708037879275063189047108172, []),
   (172699936462994638318688398374106398111710221687787489888308746668550463656965689440295683716894845928756611433381220815677160605767291842151552129770976846074231313905534180603813122046267440409673610248576676422973877376132902848972827321272130147058770010700, []),
   (6405796665518665895078790758805024104989937061794295242711106107447855264967671591613710615376127360523275191107834701789163414844083755337056843943165410479126132928798528969657480515110593100, []),
   (27512687183228520896913973652294602571423450089504829146812583107474400388377563983249154958248501752578268392616300053558369553955020668257524601628871120726262431573553116319119066550946272615747838540, []),
   (1491465760748522797384949112032778585560139515854952680578247203363071955965755412265125339705526679876091701702176290980811094596070180492721694508373134393700120446413909379666174540, []),
   (6405796665518665895078790758805024104989937061794295242711106107447855264967671591613710615376127360523275191107834701789163414844083755337056843943165410479126132907105388892210850658280825420, []),
   (1491465760748522797384949112032778585560139515854952680578247203363071955965755412265125339705526679876091701702176290980811094596070180492721694508373134393700096834581495031440106060, []),
   (6405796665518665895078790758805024104989937061794295242711106107447855264967671591613710615376127360523275191107834701789163414844083755337056843943165410479126132907105365280378436310054756940, []),
   (297634642349538514324704175597681126997417192040467897483678914397804822253879923383284425526288781339367909316149170765556657606240325285563616485964, []),
   (4993480683780955155144656090104225366759099672976410657149537621497481428794950312664813596490460562907344718065446926154629404030451833609343052639470641740, []),
   (320227140582394429650577826068134584819209220144992056842381266941485280356198748821957923680241776536584094908672591862986651273602180594709305959133662830944844, []),
   (11696541816650300215214752022706065902162560558025510489619272010858215166000075377413653796953486398106538800927777084793359887285264920862265994324226327382707890228433887428609924212201728456668695678004302745462076520445891895160817714181907413156446693363573324, []),
   (122439790100708214411404790631184963914795818913886888428922381360675449191703035839243683263963507993244905122813426090698076331963506375559030956621400425515580866300902640141400271638553146126718697472342647372, []),
   (1278331055047924519717040655700741577037933615462247725988960598406055637978873155215519264257846889111720571376383090932535340367171252136357165535372170256972, []),
   (9700679588311324277350783209123555318605828852232017064918210363766643759269813918451353040324558975985772498112854396559297017648722709421444388381710995210004152249431425241840888907369346037555202753395004199702377705042793311571733668428, []),
   (10636383194724617320682002740755429133037484763228580305584890747238064550164143344004462867926427706827685326293555385720796894009982346823080081317994480209938054014291325307421768348805084196707916965019373245345350299653643231108507548794998647185996, []),
   (845048374029366355020829968355015410437994222864502444056095737688456781153288078867242854765554579545105385613859045924013463965181541726635743769074428757650329258427858111893539503563264292181918633005603363300904511367314619537181788497518527172612447195160290009371356364038732, []),
   (635743737499570947840460928393121321360151599659877470366479834399810765407506524959627872850710297050203586436324025732910089348626691484643779436983811782082832121818737884649284495433357461917217767646494995231695025280045464842206070184895052, []),
   (2483373974607699015001800501535630161563092186171396368619061853124260802373072363123546378323087097852357759516890725519180036518073013611889763425718014773761062975854444861911267560286552585614131904869121075123808692500140551293536217883212, []),
   (326343745222657344184731151930983217933635095887432070723588505346266590950512821261967102701206323662224861815322190921423677945675758218110651947447461673198156, []),
   (19451603008667072307153412814970038597441597822186483696842741046342379591087467073357706247040630186662142679419603193989994523250703351856787258499424844, []),
   (91857598086215731215573718145170156430937517931518023633221450271957225463765963743017724253537983209940374795849573940987640179394910956915229425092884766387602600771061572172, []),
   (51989558076288528109431186203688161693596738436815574463553430433388605806796406700534688559678058422860, []),
   (162322125417717354103539475908042047320809564721494365051797891763361826009188083270137437310623312002389568540490187905121161982299096802342436438018495124942815855265789975830691562356885960471053313317817624834630675352267201433098451627063140940, []),
   (393025636033100, []), (125353248006072630288555288271693059744332, []),
   (121541389393052762314851990507999404279222748544047723844813480524, []),
   (28298559922969564450796623757721487448006547452107448908, []),
   (35291329353814753176214396833692251357626715144597561932, []),
   (168452009286192075921636420375493040926578088978900599258425588191554488263244, []),
   (161658434011133078258792495374239738066030679284814678091382516095022699143756, []),
   (34237349847258110842626472771157683940195988674664227404, []),
   (573591526811827152808495975196187797448002038284181386543614830741912192853022031503948, []),
   (100178257981531719000666588693879843226560174125465848696178182438571880280488461282614971781325019162945832955840366523451056761172263508075911923864640187831883486485267239108797321208396, []),
   (133159745078015658685716199318416905333866682370480420762166556974869716018947979317524139562626534059813554074026391406725008880335512158458029798834762404351649255744621912873327847733780483153188431961850870669427748921932, []),
   (111347874144006723251740315082759635432460193350070178465876226008240253253465016690222180042393683791803340490905319758907230252916336761275678474809718916962527428299625195504490967045906801319764556, []),
   (430262341800929705094524800640097281340494260320208923077322999007530043461153300120257957953120329791714894123603199281580754447563722731946593052494625609350222264187235867200788558066755987857996, []),
   (1912738769623910984645076069494055500, []),
   (1680712272659881660525487502500380007858136978300551644199099741259326499412807955217462405939232220105290106957352375276471186762109666258078623427599189099712729782684471337612895563655448126028, []),
   (1045909815045116443415854672273274136195051649415069756085133503123906689702611940791514591009503087375931753621166504367266926131176012, []),
   (23752297, [.ctor ⟨⟨"SortTCell"⟩⟩ [], .ctor ⟨⟨"SortTCellOpt"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortKCell"⟩⟩ [], .ctor ⟨⟨"SortKCellOpt"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortInCell"⟩⟩ [], .ctor ⟨⟨"SortInCellOpt"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortOutCell"⟩⟩ [], .ctor ⟨⟨"SortOutCellOpt"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortGeneratedCounterCell"⟩⟩ [], .ctor ⟨⟨"SortGeneratedCounterCellOpt"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortInt"⟩⟩ [], .ctor ⟨⟨"SortIOInt"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortIOError"⟩⟩ [], .ctor ⟨⟨"SortIOInt"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortString"⟩⟩ [], .ctor ⟨⟨"SortIOString"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortIOError"⟩⟩ [], .ctor ⟨⟨"SortIOString"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortIOError"⟩⟩ [], .ctor ⟨⟨"SortIOFile"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortKConfigVar"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortMap"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortSet"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortList"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortBool"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortInt"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortFloat"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortString"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortIOError"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortIOFile"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortIOInt"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortIOString"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortStream"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortGeneratedTopCell"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortGeneratedTopCellFragment"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortTCell"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortTCellOpt"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortTCellFragment"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortKCell"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortKCellOpt"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortInCell"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortInCellOpt"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortOutCell"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortOutCellOpt"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortGeneratedCounterCell"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortGeneratedCounterCellOpt"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []]),
   (23752297, [.ctor ⟨⟨"SortExp"⟩⟩ [], .ctor ⟨⟨"SortKItem"⟩⟩ []])]

/-- The literal is `gHeads` with each name coded. -/
theorem gCodes_eq : gHeads.map (fun g => (KoreAML.Distinct.strCode g.1, g.2)) = gCodes := by
  decide +kernel

/-- `absentPL` with each head compared with Γ's by the code of its name (a number), and by its
sort arguments only where the codes are equal. -/
noncomputable def absentPC (ad : AxiomDecl) : Bool :=
  (classOf "no direction").contains ad.index !=
    (appHeadsOf ad.ax.pattern).all (fun h =>
      gCodes.any fun g => g.1 == KoreAML.Distinct.strCode h.1 && decide (g.2 = h.2))

/-- Two heads are equal exactly where their names' codes and their sort arguments are
(`strCode_inj`). -/
theorem headCode_eq (g h : String × List Kore.KSort) :
    (KoreAML.Distinct.strCode g.1 == KoreAML.Distinct.strCode h.1 && decide (g.2 = h.2)) = decide (g = h) := by
  obtain ⟨g1, g2⟩ := g
  obtain ⟨h1, h2⟩ := h
  by_cases e : g1 = h1
  · subst e; simp
  · have hc : KoreAML.Distinct.strCode g1 ≠ KoreAML.Distinct.strCode h1 :=
      fun hc => e (KoreAML.Distinct.strCode_inj hc)
    simp [hc, e]

/-- `absentPC` is `absentPL`: the membership in `gCodes` is the membership in `gHeads`. -/
theorem absentPC_eq : absentPC = absentPL := by
  funext ad; unfold absentPC absentPL; rw [← gCodes_eq]
  simp only [List.any_map, Function.comp_def, headCode_eq]

theorem absentE_0 : (((U.all).drop 0).take 40).all absentPC = true := by decide +kernel
theorem absentE_40 : (((U.all).drop 40).take 40).all absentPC = true := by decide +kernel
theorem absentE_80 : (((U.all).drop 80).take 40).all absentPC = true := by decide +kernel
theorem absentE_120 : (((U.all).drop 120).take 40).all absentPC = true := by decide +kernel
theorem absentE_160 : (((U.all).drop 160).take 40).all absentPC = true := by decide +kernel
theorem absentE_200 : (((U.all).drop 200).take 40).all absentPC = true := by decide +kernel
theorem absentE_240 : (((U.all).drop 240).take 40).all absentPC = true := by decide +kernel
theorem absentE_280 : (((U.all).drop 280).take 40).all absentPC = true := by decide +kernel
theorem absentE_320 : (((U.all).drop 320).take 40).all absentPC = true := by decide +kernel
theorem absentE_360 : (((U.all).drop 360).take 40).all absentPC = true := by decide +kernel
theorem absentE_400 : (((U.all).drop 400).take 40).all absentPC = true := by decide +kernel
theorem absentE_440 : (((U.all).drop 440).take 40).all absentPC = true := by decide +kernel
theorem absentE_480 : (((U.all).drop 480).take 40).all absentPC = true := by decide +kernel
theorem absentE_520 : (((U.all).drop 520).take 40).all absentPC = true := by decide +kernel
theorem absentE_560 : (((U.all).drop 560).take 40).all absentPC = true := by decide +kernel
theorem absentE_600 : (((U.all).drop 600).take 40).all absentPC = true := by decide +kernel
theorem absentE_640 : (((U.all).drop 640).take 40).all absentPC = true := by decide +kernel
theorem absentE_680 : (((U.all).drop 680).take 40).all absentPC = true := by decide +kernel
theorem absentE_720 : (((U.all).drop 720).take 40).all absentPC = true := by decide +kernel
theorem absentE_760 : (((U.all).drop 760).take 40).all absentPC = true := by decide +kernel
theorem absentE_800 : (((U.all).drop 800).take 40).all absentPC = true := by decide +kernel
theorem absentE_840 : (((U.all).drop 840).take 40).all absentPC = true := by decide +kernel
theorem absentE_880 : (((U.all).drop 880).take 40).all absentPC = true := by decide +kernel
theorem absentE_920 : (((U.all).drop 920).take 40).all absentPC = true := by decide +kernel
theorem absentE_960 : (((U.all).drop 960).take 40).all absentPC = true := by decide +kernel
theorem absentE_1000 : (((U.all).drop 1000).take 40).all absentPC = true := by decide +kernel
theorem absentE_1040 : (((U.all).drop 1040).take 40).all absentPC = true := by decide +kernel
theorem absentE_1080 : (((U.all).drop 1080).take 40).all absentPC = true := by decide +kernel
theorem absentE_1120 : (((U.all).drop 1120).take 40).all absentPC = true := by decide +kernel
theorem absentE_1160 : (((U.all).drop 1160).take 40).all absentPC = true := by decide +kernel
theorem absentE_1200 : (((U.all).drop 1200).take 40).all absentPC = true := by decide +kernel
theorem absentE_1240 : (((U.all).drop 1240).take 40).all absentPC = true := by decide +kernel
theorem absentE_1280 : (((U.all).drop 1280).take 40).all absentPC = true := by decide +kernel
theorem absentE_1320 : (((U.all).drop 1320).take 40).all absentPC = true := by decide +kernel
theorem absentE_1360 : (((U.all).drop 1360).take 40).all absentPC = true := by decide +kernel
theorem absentE_1400 : (((U.all).drop 1400).take 40).all absentPC = true := by decide +kernel
theorem absentE_1440 : (((U.all).drop 1440).take 40).all absentPC = true := by decide +kernel
theorem absentE_1480 : (((U.all).drop 1480).take 40).all absentPC = true := by decide +kernel
theorem absentE_1520 : (((U.all).drop 1520).take 40).all absentPC = true := by decide +kernel
theorem absentE_1560 : (((U.all).drop 1560).take 40).all absentPC = true := by decide +kernel
theorem absentE_1600 : (((U.all).drop 1600).take 40).all absentPC = true := by decide +kernel
theorem absentE_1640 : (((U.all).drop 1640).take 40).all absentPC = true := by decide +kernel
theorem absentE_1680 : (((U.all).drop 1680).take 40).all absentPC = true := by decide +kernel
theorem absentE_1720 : (((U.all).drop 1720).take 40).all absentPC = true := by decide +kernel
theorem absentE_1760 : (((U.all).drop 1760).take 40).all absentPC = true := by decide +kernel
theorem absentE_1800 : (((U.all).drop 1800).take 40).all absentPC = true := by decide +kernel
theorem absentE_1840 : (((U.all).drop 1840).take 40).all absentPC = true := by decide +kernel
theorem absentE_1880 : (((U.all).drop 1880).take 40).all absentPC = true := by decide +kernel
theorem absentE_1920 : (((U.all).drop 1920).take 40).all absentPC = true := by decide +kernel
theorem absentE_1960 : (((U.all).drop 1960).take 40).all absentPC = true := by decide +kernel
theorem absentE_2000 : (((U.all).drop 2000).take 40).all absentPC = true := by decide +kernel
theorem absentE_2040 : (((U.all).drop 2040).take 40).all absentPC = true := by decide +kernel
theorem absentE_2080 : (((U.all).drop 2080).take 40).all absentPC = true := by decide +kernel
theorem absentE_2120 : (((U.all).drop 2120).take 40).all absentPC = true := by decide +kernel
theorem absentE_2160 : (((U.all).drop 2160).take 40).all absentPC = true := by decide +kernel
theorem absentE_2200 : (((U.all).drop 2200).take 40).all absentPC = true := by decide +kernel
theorem absentE_2240 : (((U.all).drop 2240).take 40).all absentPC = true := by decide +kernel
theorem absentE_2280 : (((U.all).drop 2280).take 40).all absentPC = true := by decide +kernel
theorem absentE_2320 : (((U.all).drop 2320).take 40).all absentPC = true := by decide +kernel
theorem absentE_2360 : (((U.all).drop 2360).take 40).all absentPC = true := by decide +kernel
theorem absentE_2400 : (((U.all).drop 2400).take 40).all absentPC = true := by decide +kernel
theorem absentE_2440 : (((U.all).drop 2440).take 40).all absentPC = true := by decide +kernel
theorem absentE_2480 : (((U.all).drop 2480).take 40).all absentPC = true := by decide +kernel
theorem absentE_2520 : (((U.all).drop 2520).take 40).all absentPC = true := by decide +kernel
theorem absentE_2560 : (((U.all).drop 2560).take 40).all absentPC = true := by decide +kernel
theorem absentE_2600 : (((U.all).drop 2600).take 40).all absentPC = true := by decide +kernel
theorem absentE_2640 : (((U.all).drop 2640).take 40).all absentPC = true := by decide +kernel
theorem absentE_2680 : (((U.all).drop 2680).take 40).all absentPC = true := by decide +kernel
theorem absentE_2720 : (((U.all).drop 2720).take 40).all absentPC = true := by decide +kernel
theorem absentE_2760 : (((U.all).drop 2760).take 40).all absentPC = true := by decide +kernel
theorem absentE_2800 : (((U.all).drop 2800).take 40).all absentPC = true := by decide +kernel
theorem absentE_2840 : (((U.all).drop 2840).take 40).all absentPC = true := by decide +kernel
theorem absentE_2880 : (((U.all).drop 2880).take 40).all absentPC = true := by decide +kernel
theorem absentE_2920 : (((U.all).drop 2920).take 40).all absentPC = true := by decide +kernel
theorem absentE_2960 : ((U.all).drop 2960).all absentPC = true := by decide +kernel

/-- **A sentence outside the no-direction class applies only symbols Γ has**, each a head with its
sort arguments (`appHeadsOf`) among Γ's (`gammaHeads`), and each sentence of that class applies one
Γ lacks. -/
theorem account_absent : userAxioms.all (fun ad =>
    (classOf "no direction").contains ad.index != (appHeadsOf ad.ax.pattern).all (gammaHasHead c)) = true := by
  rw [userAxioms_eq]
  have h : (U.all).all absentPC = true :=
    tieAll_whole (l := U.all) (p := absentPC) <|
      tieAll_range (l := U.all) (p := absentPC) (a := 0) (n := 40) absentE_0 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 40) (n := 40) absentE_40 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 80) (n := 40) absentE_80 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 120) (n := 40) absentE_120 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 160) (n := 40) absentE_160 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 200) (n := 40) absentE_200 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 240) (n := 40) absentE_240 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 280) (n := 40) absentE_280 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 320) (n := 40) absentE_320 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 360) (n := 40) absentE_360 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 400) (n := 40) absentE_400 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 440) (n := 40) absentE_440 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 480) (n := 40) absentE_480 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 520) (n := 40) absentE_520 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 560) (n := 40) absentE_560 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 600) (n := 40) absentE_600 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 640) (n := 40) absentE_640 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 680) (n := 40) absentE_680 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 720) (n := 40) absentE_720 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 760) (n := 40) absentE_760 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 800) (n := 40) absentE_800 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 840) (n := 40) absentE_840 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 880) (n := 40) absentE_880 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 920) (n := 40) absentE_920 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 960) (n := 40) absentE_960 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 1000) (n := 40) absentE_1000 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 1040) (n := 40) absentE_1040 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 1080) (n := 40) absentE_1080 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 1120) (n := 40) absentE_1120 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 1160) (n := 40) absentE_1160 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 1200) (n := 40) absentE_1200 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 1240) (n := 40) absentE_1240 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 1280) (n := 40) absentE_1280 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 1320) (n := 40) absentE_1320 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 1360) (n := 40) absentE_1360 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 1400) (n := 40) absentE_1400 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 1440) (n := 40) absentE_1440 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 1480) (n := 40) absentE_1480 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 1520) (n := 40) absentE_1520 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 1560) (n := 40) absentE_1560 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 1600) (n := 40) absentE_1600 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 1640) (n := 40) absentE_1640 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 1680) (n := 40) absentE_1680 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 1720) (n := 40) absentE_1720 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 1760) (n := 40) absentE_1760 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 1800) (n := 40) absentE_1800 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 1840) (n := 40) absentE_1840 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 1880) (n := 40) absentE_1880 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 1920) (n := 40) absentE_1920 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 1960) (n := 40) absentE_1960 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 2000) (n := 40) absentE_2000 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 2040) (n := 40) absentE_2040 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 2080) (n := 40) absentE_2080 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 2120) (n := 40) absentE_2120 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 2160) (n := 40) absentE_2160 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 2200) (n := 40) absentE_2200 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 2240) (n := 40) absentE_2240 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 2280) (n := 40) absentE_2280 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 2320) (n := 40) absentE_2320 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 2360) (n := 40) absentE_2360 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 2400) (n := 40) absentE_2400 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 2440) (n := 40) absentE_2440 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 2480) (n := 40) absentE_2480 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 2520) (n := 40) absentE_2520 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 2560) (n := 40) absentE_2560 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 2600) (n := 40) absentE_2600 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 2640) (n := 40) absentE_2640 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 2680) (n := 40) absentE_2680 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 2720) (n := 40) absentE_2720 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 2760) (n := 40) absentE_2760 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 2800) (n := 40) absentE_2800 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 2840) (n := 40) absentE_2840 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 2880) (n := 40) absentE_2880 <|
      tieAll_range (l := U.all) (p := absentPC) (a := 2920) (n := 40) absentE_2920 <|
      absentE_2960
  rw [absentPC_eq, absentPL_eq] at h; exact h

/-- **The no-direction class is closed**: every sentence outside it applies only symbols Γ has,
so no sentence with a direction applies a symbol Γ lacks. The injection `inj` is no member of
`kernelSyms` and is Γ's all the same at each subsort pair, where the constructor items state it
(`gammaHeads`). -/
theorem absent_closed :
    (userAxioms.filter (fun ad => !(classOf "no direction").contains ad.index)).all
      (fun ad => (appHeadsOf ad.ax.pattern).all (gammaHasHead c)) = true :=
  tieAbsent_of_account userAxioms _ _ account_absent

/-- The sentences of the no-direction class that are equations of a projection `project:X` (their
left side applies `Lblproject'Coln'X`), each with X. -/
def absentProj : List (Nat × String) :=
  [(2963, "Bool"), (2964, "Exp"), (2965, "Float"), (2966, "GeneratedCounterCell"),
   (2967, "GeneratedCounterCellOpt"), (2968, "GeneratedTopCell"),
   (2969, "GeneratedTopCellFragment"), (2970, "IOError"), (2971, "IOFile"), (2972, "IOInt"),
   (2973, "IOString"), (2974, "InCell"), (2975, "InCellOpt"), (2977, "K"), (2978, "KCell"),
   (2979, "KCellOpt"), (2980, "KItem"), (2981, "List"), (2982, "Map"), (2983, "OutCell"),
   (2984, "OutCellOpt"), (2985, "Set"), (2986, "Stream"), (2987, "String"), (2988, "TCell"),
   (2989, "TCellFragment"), (2990, "TCellOpt")]

/-- Each sort of `absentProj` is K, KItem or a sort below KItem of Γ, with K and KItem
constructor sorts. -/
theorem absent_proj_below_c : absentProj.all (fun p => GenEqs.projBelowB c p.2) = true := by
  decide +kernel

/-- **The projections the no-direction class defines are of sorts below KItem**: `absentProj` is
the list of the no-direction sentences whose left side applies a symbol `Lblproject'Coln'X`, each
with that X, and each such X is K, KItem or a sort below KItem of Γ, with K and KItem constructor
sorts (`GenEqs.projBelowB`). So the pattern each of these equations is at is functional and
injective on X in every model of Γ (`GenEqs.projSel_fun`, `GenEqs.projSel_inj`): what the
equation states of the pattern's symbols, Γ entails. -/
theorem absent_proj_below (H : HookParams) :
    (userAxioms.filter (fun ad => (classOf "no direction").contains ad.index &&
        ((AttrsAgree.eqnHead ad.ax.pattern).getD "").startsWith "Lblproject'Coln'")).map
      (fun ad => (ad.index, AttrsAgree.eqnHead ad.ax.pattern)) =
      absentProj.map (fun p => (p.1, some ("Lblproject'Coln'" ++ p.2))) ∧
    absentProj.all (fun p => GenEqs.projBelowB (cH H) p.2) = true :=
  ⟨by rw [userAxioms_eq]; decide +kernel, absent_proj_below_c⟩

end KCore.TieE2CellsStream

#check @KCore.TieE2CellsStream.account_absent
#check @KCore.TieE2CellsStream.absent_closed
#check @KCore.TieE2CellsStream.absent_proj_below_c
#check @KCore.TieE2CellsStream.absent_proj_below
#print axioms KCore.TieE2CellsStream.account_absent
#print axioms KCore.TieE2CellsStream.absent_closed
#print axioms KCore.TieE2CellsStream.absent_proj_below_c
#print axioms KCore.TieE2CellsStream.absent_proj_below
