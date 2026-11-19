/-
  The tie (C14) on `f2-examples/rdr-config-deep.kompile.kore`, the kompiled text of construct fixture rdr-config-deep
  (`test/constructs/fixtures/rdr-config-deep`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `TIEGEN_PROBE_TIMEOUT=3000 python3 -I test/constructs/tiegen.py rdr-config-deep --split --cons-head
  --wf-parts --sig-chunk-first 13 --account-sorted --heads-literal --heads-codes --chunk 50
  --attrs-blocks 50 --decl-parts --fn-blocks 27 --absent-file --decl-syms-literal --nojunk-eq
  --nojunk-blocks 25`;
  run from the package root: `lake env lean -j1 test/TieRdrConfigDeep.lean`
  (166 s, peak 5.3 GiB under a 12 GiB scope with one Lean thread).

  Layer 1.
  - `wf_defn`: `wf defn = true`.
  - The account: the class lists partition the 1707 sentences of the user module RDR-CONFIG-DEEP, in
    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds
    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  - `absent_proj_below`: the 202 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_agree`: the attributes the translation does not read agree with `defn`.
  - `sig_origin_but_next`: each of the 770 items of `sigItems c` but one is a declaration's item
    of the text or a surplus one; the one is next's arity at the configuration sort, which Γ states
    and the text, having no `\rewrites` (`text_nextless`), does not. `decls_entailed`: Γ entails
    the item of each declaration without sort parameters of a symbol Γ has (by ranges of the lists).
  - The definition reads no confined sort (`readsConfined_c`), has no open generator (`noRaw`) and
    owes no fact (`term_named`, `total_named`, `agree_named`, `match_named`), so Γ with the step's
    closure has a model for every H (`consistent`).

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (405): each of Γ's items is the translation of one sentence, in the
    order `fnText` lists them (`fn_shape`); `fns_entailed` (E), `fns_from_text` (the converse),
    `fn_prios` (the priorities the sentences state are the clauses').
  - Constructor sentences (591): entailed by Γ (`cons_entailed`).
  - No junk (3 of a sort without generators, `nojunk_trivial_entailed`; 195 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (550): Γ with it has no model (`idem_refuted`).
  - The converse over Γ's content: each premise is a function sentence's translation, one of the
    five parts Γ defines by predicates, or definedness (`gamma_origin`, `gamma_from`).
  - Hooked functional, collection law, library: at values (no theorem here); function functional:
    owed as `FnHyp` (no theorem); no direction: `absent_closed`.

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (1586);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (0).
  Written with `--split`: this file holds the literals, the names, `wf`, the account, the
  consistency and the sections that read none of the other files' decisions; the other sections are
  in `test/TieRdrConfigDeepAttrs.lean`, `test/TieRdrConfigDeepSig.lean`,
  `test/TieRdrConfigDeepDecls.lean`, `test/TieRdrConfigDeepFns.lean`,
  `test/TieRdrConfigDeepNoJunk.lean`, `test/TieRdrConfigDeepCons.lean`,
  `test/TieRdrConfigDeepAbsent.lean`, `test/TieRdrConfigDeepDeclCounts.lean`, in this namespace,
  each of which repeats the literals and the definitions and facts it reads, as a test file imports
  no test file.
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

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads no confined sort: its theory is Γ. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "RDR-CONFIG-DEEP")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 1707 := by decide +kernel

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl

/-! ## Layer 1 -/

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-! `wf defn` conjunct by conjunct (`wf_of_parts_all`), each a decision of its own; the names
declared once by their codes (`KoreAML.Distinct.codesDistinct`), sorted in as many passes as the
bits of the text's number of declarations. -/
theorem sorts_distinct : KoreAML.Distinct.codesDistinct 9 (defn.emit.sortDecls.map (·.name)) = true := by
  decide +kernel
theorem syms_distinct :
    KoreAML.Distinct.codesDistinct 11 (defn.emit.symbolDecls.map (·.name) ++ defn.emit.aliasNames) = true := by
  decide +kernel
theorem names_rest : (c.hooksApart && c.predsApart && c.idsOK) = true := by decide_cheap
theorem okAll_c : c.okAll = true := by decide_cheap
theorem cert_ok : defn.cert.ok c = true := by decide +kernel
theorem pres_ok : defn.pres.ok c = true := by decide +kernel
theorem params_ok : defn.paramsOK = true := by decide +kernel
theorem faith_ok : c.faithOK = true := by unfold Semantics.faithOK; decide_cheap
theorem overloads_ok : c.overloadsOK = true := by decide +kernel
theorem wf_defn : wf defn = true :=
  wf_of_parts_all sorts_distinct syms_distinct names_rest okAll_c cert_ok pres_ok params_ok faith_ok overloads_ok

/-! ## The account: every sentence of the user module is in exactly one class -/

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

/-- The indices of the user module's sentences, in text order, are 4, …, 1710. -/
theorem indices_eq : U.all.map (·.index) = List.range' 4 1707 := by decide +kernel

/-- The class lists, sorted (12 passes of `KoreAML.Distinct.msort`), are the same range. -/
theorem classes_sorted : KoreAML.Distinct.msort 12 (classes.flatMap (·.2)) = List.range' 4 1707 := by
  decide +kernel

/-- **The account**: the class lists partition the user module's sentences. Their concatenation is
a permutation of the sentences' indices, which are distinct, so each sentence is in one class and
in it once: sorted, the class lists are the range the indices are (`tacAccount_of_msort`). -/
theorem account : (classes.flatMap (·.2)).isPerm (userAxioms.map (·.index)) = true ∧
    (userAxioms.map (·.index)).Nodup :=
  tacAccount_of_msort classes_sorted (by rw [userAxioms_eq]; exact indices_eq)

/-- The class sizes. -/
theorem account_sizes : classes.map (fun cl => (cl.1, cl.2.length)) =
    [("function equation", 405), ("rewrite rule", 0), ("priority equation", 0), ("constructor functional", 195), ("subsort", 266), ("injectivity", 130), ("distinctness", 0), ("no junk", 199), ("function functional", 203), ("hooked functional", 23), ("collection law", 9), ("library", 2), ("set idempotence", 1), ("set-variable lemma", 1), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter functional", 0), ("parameter lemma", 0), ("user lemma", 0), ("user lemma at values", 0), ("no direction", 273)] := by
  decide +kernel

/-- The classes are the tie's (`tieClasses`, which gives each its direction), in its order. -/
theorem account_classes : classes.map (·.1) = tieClasses.map (·.1) := by decide +kernel

/-- The sentences whose text is none of f2-examples/ens.kompile.kore's user module, with their class. -/
def unmapped : List (Nat × String) :=
  [(4, "subsort"), (5, "subsort"), (6, "subsort"), (7, "subsort"), (8, "subsort"), (9, "subsort"),
   (10, "subsort"), (11, "subsort"), (12, "subsort"), (13, "subsort"), (14, "subsort"),
   (15, "subsort"), (16, "subsort"), (17, "subsort"), (18, "subsort"), (19, "subsort"),
   (20, "subsort"), (21, "subsort"), (22, "subsort"), (23, "subsort"), (25, "subsort"),
   (26, "subsort"), (27, "subsort"), (28, "subsort"), (29, "subsort"), (30, "subsort"),
   (31, "subsort"), (32, "subsort"), (34, "subsort"), (35, "subsort"), (36, "subsort"),
   (37, "subsort"), (38, "subsort"), (39, "subsort"), (40, "subsort"), (41, "subsort"),
   (42, "subsort"), (44, "subsort"), (45, "subsort"), (46, "subsort"), (47, "subsort"),
   (48, "subsort"), (50, "subsort"), (51, "subsort"), (52, "subsort"), (53, "subsort"),
   (54, "subsort"), (55, "subsort"), (56, "subsort"), (57, "subsort"), (58, "subsort"),
   (59, "subsort"), (60, "subsort"), (62, "subsort"), (63, "subsort"), (64, "subsort"),
   (65, "subsort"), (66, "subsort"), (67, "subsort"), (68, "subsort"), (69, "subsort"),
   (70, "subsort"), (71, "subsort"), (72, "subsort"), (73, "subsort"), (74, "subsort"),
   (75, "subsort"), (76, "subsort"), (77, "subsort"), (78, "subsort"), (79, "subsort"),
   (80, "subsort"), (81, "subsort"), (82, "subsort"), (83, "subsort"), (84, "subsort"),
   (85, "subsort"), (86, "subsort"), (88, "subsort"), (89, "subsort"), (91, "subsort"),
   (92, "subsort"), (93, "subsort"), (94, "subsort"), (95, "subsort"), (97, "subsort"),
   (98, "subsort"), (99, "subsort"), (100, "subsort"), (101, "subsort"), (102, "subsort"),
   (103, "subsort"), (104, "subsort"), (105, "subsort"), (106, "subsort"), (107, "subsort"),
   (109, "subsort"), (110, "subsort"), (111, "subsort"), (112, "subsort"), (113, "subsort"),
   (114, "subsort"), (115, "subsort"), (116, "subsort"), (117, "subsort"), (118, "subsort"),
   (119, "subsort"), (120, "subsort"), (121, "subsort"), (122, "subsort"), (123, "subsort"),
   (124, "subsort"), (126, "subsort"), (127, "subsort"), (128, "subsort"), (129, "subsort"),
   (130, "subsort"), (131, "subsort"), (132, "subsort"), (133, "subsort"), (134, "subsort"),
   (135, "subsort"), (136, "subsort"), (137, "subsort"), (138, "subsort"), (139, "subsort"),
   (140, "subsort"), (141, "subsort"), (142, "subsort"), (143, "subsort"), (144, "subsort"),
   (145, "subsort"), (146, "subsort"), (147, "subsort"), (148, "subsort"), (149, "subsort"),
   (150, "subsort"), (151, "subsort"), (152, "subsort"), (153, "subsort"), (154, "subsort"),
   (155, "subsort"), (156, "subsort"), (157, "subsort"), (158, "subsort"), (159, "subsort"),
   (160, "subsort"), (161, "subsort"), (162, "subsort"), (163, "subsort"), (164, "subsort"),
   (165, "subsort"), (166, "subsort"), (167, "subsort"), (168, "subsort"), (169, "subsort"),
   (170, "subsort"), (171, "subsort"), (172, "subsort"), (173, "subsort"), (174, "subsort"),
   (175, "subsort"), (176, "subsort"), (177, "subsort"), (178, "subsort"), (179, "subsort"),
   (180, "subsort"), (181, "subsort"), (182, "subsort"), (183, "subsort"), (184, "subsort"),
   (185, "subsort"), (187, "subsort"), (188, "subsort"), (189, "subsort"), (190, "subsort"),
   (191, "subsort"), (192, "subsort"), (193, "subsort"), (194, "subsort"), (195, "subsort"),
   (196, "subsort"), (197, "subsort"), (198, "subsort"), (199, "subsort"), (200, "subsort"),
   (201, "subsort"), (202, "subsort"), (203, "subsort"), (204, "subsort"), (205, "subsort"),
   (206, "subsort"), (208, "subsort"), (209, "subsort"), (210, "subsort"), (211, "subsort"),
   (212, "subsort"), (213, "subsort"), (215, "subsort"), (216, "subsort"), (217, "subsort"),
   (218, "subsort"), (219, "subsort"), (220, "subsort"), (221, "subsort"), (222, "subsort"),
   (223, "subsort"), (224, "subsort"), (225, "subsort"), (226, "subsort"), (227, "subsort"),
   (228, "subsort"), (229, "subsort"), (230, "subsort"), (231, "subsort"), (232, "subsort"),
   (233, "subsort"), (234, "subsort"), (235, "subsort"), (236, "subsort"), (237, "subsort"),
   (238, "subsort"), (239, "subsort"), (240, "subsort"), (241, "subsort"), (242, "subsort"),
   (243, "subsort"), (244, "subsort"), (245, "subsort"), (246, "subsort"), (247, "subsort"),
   (248, "subsort"), (249, "subsort"), (250, "subsort"), (251, "subsort"), (252, "subsort"),
   (253, "subsort"), (254, "subsort"), (255, "subsort"), (256, "subsort"), (257, "subsort"),
   (258, "subsort"), (259, "subsort"), (260, "subsort"), (261, "subsort"), (262, "subsort"),
   (263, "subsort"), (264, "subsort"), (265, "subsort"), (266, "subsort"), (267, "subsort"),
   (268, "subsort"), (273, "constructor functional"), (274, "injectivity"),
   (275, "constructor functional"), (276, "injectivity"), (277, "constructor functional"),
   (278, "injectivity"), (279, "constructor functional"), (280, "injectivity"),
   (281, "constructor functional"), (282, "injectivity"), (283, "constructor functional"),
   (284, "injectivity"), (285, "constructor functional"), (286, "injectivity"),
   (287, "constructor functional"), (288, "injectivity"), (289, "constructor functional"),
   (290, "injectivity"), (291, "constructor functional"), (292, "injectivity"),
   (293, "constructor functional"), (294, "injectivity"), (295, "constructor functional"),
   (296, "injectivity"), (297, "constructor functional"), (298, "injectivity"),
   (299, "constructor functional"), (300, "injectivity"), (301, "constructor functional"),
   (302, "injectivity"), (303, "constructor functional"), (304, "injectivity"),
   (305, "constructor functional"), (306, "injectivity"), (307, "constructor functional"),
   (308, "injectivity"), (309, "constructor functional"), (310, "injectivity"),
   (311, "constructor functional"), (312, "injectivity"), (313, "constructor functional"),
   (314, "injectivity"), (315, "constructor functional"), (316, "injectivity"),
   (317, "constructor functional"), (318, "injectivity"), (319, "constructor functional"),
   (320, "injectivity"), (321, "constructor functional"), (322, "injectivity"),
   (323, "constructor functional"), (324, "injectivity"), (325, "constructor functional"),
   (326, "injectivity"), (327, "constructor functional"), (328, "injectivity"),
   (329, "constructor functional"), (330, "injectivity"), (331, "constructor functional"),
   (332, "injectivity"), (333, "constructor functional"), (334, "injectivity"),
   (335, "constructor functional"), (336, "injectivity"), (337, "constructor functional"),
   (338, "injectivity"), (339, "constructor functional"), (340, "injectivity"),
   (341, "constructor functional"), (342, "injectivity"), (343, "constructor functional"),
   (344, "injectivity"), (345, "constructor functional"), (346, "injectivity"),
   (347, "constructor functional"), (348, "injectivity"), (349, "constructor functional"),
   (350, "injectivity"), (351, "constructor functional"), (352, "injectivity"),
   (353, "constructor functional"), (354, "injectivity"), (355, "constructor functional"),
   (356, "injectivity"), (357, "constructor functional"), (358, "injectivity"),
   (359, "constructor functional"), (360, "injectivity"), (361, "constructor functional"),
   (362, "injectivity"), (363, "constructor functional"), (364, "injectivity"),
   (365, "constructor functional"), (366, "injectivity"), (367, "constructor functional"),
   (368, "injectivity"), (369, "constructor functional"), (370, "injectivity"),
   (371, "constructor functional"), (372, "injectivity"), (373, "constructor functional"),
   (374, "injectivity"), (375, "constructor functional"), (376, "injectivity"),
   (377, "constructor functional"), (378, "injectivity"), (379, "constructor functional"),
   (380, "injectivity"), (381, "constructor functional"), (382, "injectivity"),
   (383, "constructor functional"), (384, "injectivity"), (385, "constructor functional"),
   (386, "injectivity"), (387, "constructor functional"), (388, "injectivity"),
   (389, "constructor functional"), (390, "injectivity"), (391, "constructor functional"),
   (392, "injectivity"), (393, "constructor functional"), (394, "injectivity"),
   (395, "constructor functional"), (396, "injectivity"), (397, "constructor functional"),
   (398, "injectivity"), (399, "constructor functional"), (400, "injectivity"),
   (401, "constructor functional"), (402, "injectivity"), (403, "constructor functional"),
   (404, "injectivity"), (405, "constructor functional"), (406, "injectivity"),
   (407, "constructor functional"), (408, "injectivity"), (409, "constructor functional"),
   (410, "injectivity"), (411, "constructor functional"), (412, "injectivity"),
   (413, "constructor functional"), (414, "injectivity"), (415, "constructor functional"),
   (416, "injectivity"), (417, "constructor functional"), (418, "injectivity"),
   (419, "constructor functional"), (420, "injectivity"), (421, "constructor functional"),
   (422, "injectivity"), (423, "constructor functional"), (424, "injectivity"),
   (425, "constructor functional"), (426, "injectivity"), (427, "constructor functional"),
   (428, "injectivity"), (429, "constructor functional"), (430, "injectivity"),
   (431, "constructor functional"), (432, "injectivity"), (433, "constructor functional"),
   (434, "injectivity"), (435, "constructor functional"), (436, "injectivity"),
   (437, "constructor functional"), (438, "injectivity"), (439, "constructor functional"),
   (440, "injectivity"), (441, "constructor functional"), (442, "injectivity"),
   (443, "constructor functional"), (444, "injectivity"), (445, "constructor functional"),
   (446, "injectivity"), (447, "constructor functional"), (448, "injectivity"),
   (449, "constructor functional"), (450, "injectivity"), (451, "constructor functional"),
   (452, "injectivity"), (453, "constructor functional"), (454, "injectivity"),
   (455, "constructor functional"), (456, "injectivity"), (457, "constructor functional"),
   (458, "injectivity"), (459, "constructor functional"), (460, "injectivity"),
   (461, "constructor functional"), (462, "injectivity"), (463, "constructor functional"),
   (464, "injectivity"), (465, "constructor functional"), (466, "injectivity"),
   (467, "constructor functional"), (468, "injectivity"), (469, "constructor functional"),
   (470, "injectivity"), (471, "constructor functional"), (472, "injectivity"),
   (473, "constructor functional"), (474, "injectivity"), (475, "constructor functional"),
   (476, "injectivity"), (477, "constructor functional"), (478, "injectivity"),
   (479, "constructor functional"), (480, "injectivity"), (481, "constructor functional"),
   (482, "injectivity"), (483, "constructor functional"), (484, "injectivity"),
   (485, "constructor functional"), (486, "injectivity"), (487, "constructor functional"),
   (488, "injectivity"), (489, "constructor functional"), (490, "injectivity"),
   (491, "constructor functional"), (492, "injectivity"), (493, "constructor functional"),
   (494, "injectivity"), (495, "constructor functional"), (496, "injectivity"),
   (497, "constructor functional"), (498, "injectivity"), (499, "constructor functional"),
   (500, "injectivity"), (501, "constructor functional"), (502, "injectivity"),
   (503, "constructor functional"), (504, "injectivity"), (505, "constructor functional"),
   (506, "injectivity"), (507, "constructor functional"), (508, "injectivity"),
   (509, "constructor functional"), (510, "injectivity"), (511, "constructor functional"),
   (512, "injectivity"), (513, "constructor functional"), (514, "injectivity"),
   (515, "constructor functional"), (516, "injectivity"), (517, "constructor functional"),
   (518, "injectivity"), (519, "constructor functional"), (520, "injectivity"),
   (521, "constructor functional"), (522, "injectivity"), (523, "constructor functional"),
   (524, "injectivity"), (527, "constructor functional"), (528, "injectivity"),
   (529, "constructor functional"), (530, "injectivity"), (561, "function functional"),
   (562, "function functional"), (563, "function functional"), (564, "function functional"),
   (565, "function functional"), (566, "function functional"), (567, "function functional"),
   (568, "function functional"), (569, "function functional"), (570, "function functional"),
   (571, "function functional"), (572, "function functional"), (573, "function functional"),
   (574, "function functional"), (575, "function functional"), (576, "function functional"),
   (577, "function functional"), (578, "function functional"), (579, "function functional"),
   (580, "function functional"), (581, "function functional"), (582, "function functional"),
   (583, "function functional"), (584, "function functional"), (585, "function functional"),
   (586, "function functional"), (587, "function functional"), (588, "function functional"),
   (589, "function functional"), (590, "function functional"), (591, "function functional"),
   (592, "function functional"), (593, "function functional"), (594, "function functional"),
   (595, "function functional"), (596, "function functional"), (597, "function functional"),
   (598, "function functional"), (599, "function functional"), (600, "function functional"),
   (601, "function functional"), (602, "function functional"), (603, "function functional"),
   (604, "function functional"), (605, "function functional"), (606, "function functional"),
   (607, "function functional"), (608, "function functional"), (609, "function functional"),
   (610, "function functional"), (611, "function functional"), (612, "function functional"),
   (613, "function functional"), (614, "function functional"), (615, "function functional"),
   (616, "function functional"), (617, "function functional"), (618, "function functional"),
   (619, "function functional"), (620, "function functional"), (621, "function functional"),
   (622, "function functional"), (623, "function functional"), (624, "function functional"),
   (625, "function functional"), (626, "function functional"), (627, "function functional"),
   (628, "function functional"), (629, "function functional"), (630, "function functional"),
   (631, "function functional"), (632, "function functional"), (633, "function functional"),
   (634, "function functional"), (635, "function functional"), (636, "function functional"),
   (637, "function functional"), (638, "function functional"), (639, "function functional"),
   (640, "function functional"), (641, "function functional"), (642, "function functional"),
   (643, "function functional"), (644, "function functional"), (645, "function functional"),
   (646, "function functional"), (647, "function functional"), (648, "function functional"),
   (649, "function functional"), (650, "function functional"), (651, "function functional"),
   (652, "function functional"), (653, "function functional"), (654, "function functional"),
   (655, "function functional"), (656, "function functional"), (657, "function functional"),
   (658, "function functional"), (659, "function functional"), (660, "function functional"),
   (661, "function functional"), (662, "function functional"), (663, "function functional"),
   (664, "function functional"), (665, "function functional"), (666, "function functional"),
   (667, "function functional"), (668, "function functional"), (669, "function functional"),
   (670, "function functional"), (671, "function functional"), (672, "function functional"),
   (673, "function functional"), (674, "function functional"), (675, "function functional"),
   (676, "function functional"), (677, "function functional"), (678, "function functional"),
   (679, "function functional"), (680, "function functional"), (681, "function functional"),
   (682, "function functional"), (683, "function functional"), (684, "function functional"),
   (685, "function functional"), (686, "function functional"), (687, "function functional"),
   (688, "function functional"), (689, "function functional"), (690, "function functional"),
   (691, "function functional"), (692, "function functional"), (693, "function functional"),
   (694, "function functional"), (695, "function functional"), (696, "function functional"),
   (697, "function functional"), (698, "function functional"), (699, "function functional"),
   (700, "function functional"), (701, "function functional"), (702, "function functional"),
   (703, "function functional"), (704, "function functional"), (705, "function functional"),
   (706, "function functional"), (707, "function functional"), (708, "function functional"),
   (709, "function functional"), (710, "function functional"), (711, "function functional"),
   (712, "function functional"), (713, "function functional"), (714, "function functional"),
   (715, "function functional"), (716, "function functional"), (717, "function functional"),
   (718, "function functional"), (719, "function functional"), (720, "function functional"),
   (721, "function functional"), (722, "function functional"), (723, "function functional"),
   (724, "function functional"), (725, "function functional"), (726, "function functional"),
   (727, "function functional"), (728, "function functional"), (729, "function functional"),
   (730, "function functional"), (731, "function functional"), (732, "function functional"),
   (733, "function functional"), (734, "function functional"), (735, "function functional"),
   (736, "function functional"), (737, "function functional"), (738, "function functional"),
   (739, "function functional"), (740, "function functional"), (741, "function functional"),
   (742, "function functional"), (743, "function functional"), (744, "function functional"),
   (745, "function functional"), (746, "function functional"), (747, "function functional"),
   (748, "function functional"), (749, "function functional"), (764, "constructor functional"),
   (765, "constructor functional"), (766, "constructor functional"),
   (767, "constructor functional"), (768, "constructor functional"),
   (769, "constructor functional"), (770, "constructor functional"),
   (771, "constructor functional"), (772, "constructor functional"),
   (773, "constructor functional"), (774, "constructor functional"),
   (775, "constructor functional"), (776, "constructor functional"),
   (777, "constructor functional"), (778, "constructor functional"),
   (779, "constructor functional"), (780, "constructor functional"),
   (781, "constructor functional"), (782, "constructor functional"),
   (783, "constructor functional"), (784, "constructor functional"),
   (785, "constructor functional"), (786, "constructor functional"),
   (787, "constructor functional"), (788, "constructor functional"),
   (789, "constructor functional"), (790, "constructor functional"),
   (791, "constructor functional"), (792, "constructor functional"),
   (793, "constructor functional"), (794, "constructor functional"),
   (795, "constructor functional"), (796, "constructor functional"),
   (797, "constructor functional"), (798, "constructor functional"),
   (799, "constructor functional"), (800, "constructor functional"),
   (801, "constructor functional"), (802, "constructor functional"),
   (803, "constructor functional"), (804, "constructor functional"),
   (805, "constructor functional"), (806, "constructor functional"),
   (807, "constructor functional"), (808, "constructor functional"),
   (809, "constructor functional"), (810, "constructor functional"),
   (811, "constructor functional"), (812, "constructor functional"),
   (813, "constructor functional"), (814, "constructor functional"),
   (815, "constructor functional"), (816, "constructor functional"),
   (817, "constructor functional"), (818, "constructor functional"),
   (819, "constructor functional"), (820, "constructor functional"),
   (821, "constructor functional"), (822, "constructor functional"),
   (823, "constructor functional"), (824, "constructor functional"),
   (825, "constructor functional"), (826, "constructor functional"), (836, "no junk"),
   (837, "no junk"), (838, "no junk"), (839, "no junk"), (840, "no junk"), (841, "no junk"),
   (842, "no junk"), (843, "no junk"), (844, "no junk"), (845, "no junk"), (846, "no junk"),
   (847, "no junk"), (848, "no junk"), (849, "no junk"), (850, "no junk"), (851, "no junk"),
   (852, "no junk"), (853, "no junk"), (854, "no junk"), (855, "no junk"), (856, "no junk"),
   (857, "no junk"), (858, "no junk"), (859, "no junk"), (860, "no junk"), (861, "no junk"),
   (862, "no junk"), (863, "no junk"), (864, "no junk"), (865, "no junk"), (866, "no junk"),
   (867, "no junk"), (868, "no junk"), (869, "no junk"), (870, "no junk"), (871, "no junk"),
   (872, "no junk"), (873, "no junk"), (874, "no junk"), (875, "no junk"), (876, "no junk"),
   (877, "no junk"), (878, "no junk"), (879, "no junk"), (880, "no junk"), (881, "no junk"),
   (882, "no junk"), (883, "no junk"), (884, "no junk"), (885, "no junk"), (886, "no junk"),
   (887, "no junk"), (888, "no junk"), (889, "no junk"), (890, "no junk"), (891, "no junk"),
   (892, "no junk"), (893, "no junk"), (894, "no junk"), (895, "no junk"), (896, "no junk"),
   (897, "no junk"), (898, "no junk"), (899, "no junk"), (900, "no junk"), (901, "no junk"),
   (902, "no junk"), (903, "no junk"), (904, "no junk"), (905, "no junk"), (906, "no junk"),
   (907, "no junk"), (908, "no junk"), (909, "no junk"), (910, "no junk"), (911, "no junk"),
   (912, "no junk"), (913, "no junk"), (914, "no junk"), (915, "no junk"), (916, "no junk"),
   (917, "no junk"), (918, "no junk"), (919, "no junk"), (920, "no junk"), (921, "no junk"),
   (922, "no junk"), (923, "no junk"), (924, "no junk"), (925, "no junk"), (926, "no junk"),
   (927, "no junk"), (928, "no junk"), (929, "no junk"), (930, "no junk"), (931, "no junk"),
   (932, "no junk"), (933, "no junk"), (934, "no junk"), (935, "no junk"), (936, "no junk"),
   (937, "no junk"), (938, "no junk"), (939, "no junk"), (940, "no junk"), (941, "no junk"),
   (942, "no junk"), (943, "no junk"), (944, "no junk"), (945, "no junk"), (946, "no junk"),
   (947, "no junk"), (948, "no junk"), (949, "no junk"), (950, "no junk"), (951, "no junk"),
   (952, "no junk"), (953, "no junk"), (954, "no junk"), (955, "no junk"), (956, "no junk"),
   (957, "no junk"), (958, "no junk"), (959, "no junk"), (960, "no junk"), (961, "no junk"),
   (962, "no junk"), (963, "no junk"), (964, "no junk"), (965, "no junk"), (966, "no junk"),
   (967, "no junk"), (968, "no junk"), (969, "no junk"), (970, "no junk"), (971, "no junk"),
   (972, "no junk"), (973, "no junk"), (974, "no junk"), (975, "no junk"), (976, "no junk"),
   (977, "no junk"), (978, "no junk"), (979, "no junk"), (980, "no junk"), (981, "no junk"),
   (982, "no junk"), (983, "no junk"), (984, "no junk"), (985, "no junk"), (986, "no junk"),
   (987, "no junk"), (988, "no junk"), (989, "no junk"), (990, "no junk"), (991, "no junk"),
   (992, "no junk"), (993, "no junk"), (994, "no junk"), (995, "no junk"), (996, "no junk"),
   (997, "no junk"), (998, "no junk"), (999, "no junk"), (1000, "no junk"), (1001, "no junk"),
   (1002, "no junk"), (1003, "no junk"), (1004, "no junk"), (1005, "no junk"), (1006, "no junk"),
   (1007, "no junk"), (1008, "no junk"), (1009, "no junk"), (1010, "no junk"), (1011, "no junk"),
   (1012, "no junk"), (1013, "no junk"), (1014, "no junk"), (1015, "no junk"), (1016, "no junk"),
   (1017, "no junk"), (1018, "no junk"), (1019, "no junk"), (1020, "no junk"), (1021, "no junk"),
   (1022, "no junk"), (1023, "no junk"), (1024, "no junk"), (1027, "no junk"), (1028, "no junk"),
   (1033, "no junk"), (1035, "no direction"), (1036, "no direction"), (1037, "no direction"),
   (1038, "no direction"), (1039, "no direction"), (1040, "no direction"), (1041, "no direction"),
   (1042, "no direction"), (1043, "no direction"), (1044, "no direction"), (1045, "no direction"),
   (1046, "no direction"), (1047, "no direction"), (1048, "no direction"), (1049, "no direction"),
   (1050, "no direction"), (1051, "no direction"), (1052, "no direction"), (1053, "no direction"),
   (1054, "no direction"), (1055, "no direction"), (1056, "no direction"), (1057, "no direction"),
   (1058, "no direction"), (1059, "no direction"), (1060, "no direction"), (1061, "no direction"),
   (1062, "no direction"), (1063, "no direction"), (1064, "no direction"), (1065, "no direction"),
   (1066, "no direction"), (1067, "no direction"), (1068, "no direction"), (1069, "no direction"),
   (1070, "no direction"), (1071, "no direction"), (1072, "no direction"), (1073, "no direction"),
   (1074, "no direction"), (1075, "no direction"), (1076, "no direction"), (1077, "no direction"),
   (1078, "no direction"), (1079, "no direction"), (1080, "no direction"), (1081, "no direction"),
   (1082, "no direction"), (1083, "no direction"), (1084, "no direction"), (1085, "no direction"),
   (1086, "no direction"), (1087, "no direction"), (1088, "no direction"), (1089, "no direction"),
   (1090, "no direction"), (1091, "no direction"), (1092, "no direction"), (1093, "no direction"),
   (1094, "no direction"), (1095, "no direction"), (1096, "no direction"), (1097, "no direction"),
   (1098, "no direction"), (1100, "no direction"), (1101, "no direction"),
   (1104, "function equation"), (1105, "function equation"), (1106, "function equation"),
   (1107, "function equation"), (1108, "function equation"), (1109, "function equation"),
   (1110, "function equation"), (1111, "function equation"), (1112, "function equation"),
   (1113, "function equation"), (1114, "function equation"), (1115, "function equation"),
   (1116, "function equation"), (1117, "function equation"), (1118, "function equation"),
   (1119, "function equation"), (1120, "function equation"), (1121, "function equation"),
   (1122, "function equation"), (1123, "function equation"), (1124, "function equation"),
   (1125, "function equation"), (1126, "function equation"), (1127, "function equation"),
   (1128, "function equation"), (1129, "function equation"), (1130, "function equation"),
   (1131, "function equation"), (1132, "function equation"), (1133, "function equation"),
   (1134, "function equation"), (1135, "function equation"), (1136, "function equation"),
   (1137, "function equation"), (1138, "function equation"), (1139, "function equation"),
   (1140, "function equation"), (1141, "function equation"), (1142, "function equation"),
   (1143, "function equation"), (1144, "function equation"), (1145, "function equation"),
   (1146, "function equation"), (1147, "function equation"), (1148, "function equation"),
   (1149, "function equation"), (1150, "function equation"), (1151, "function equation"),
   (1152, "function equation"), (1153, "function equation"), (1154, "function equation"),
   (1155, "function equation"), (1156, "function equation"), (1157, "function equation"),
   (1158, "function equation"), (1159, "function equation"), (1160, "function equation"),
   (1161, "function equation"), (1162, "function equation"), (1163, "function equation"),
   (1164, "function equation"), (1165, "function equation"), (1166, "function equation"),
   (1167, "function equation"), (1168, "function equation"), (1169, "function equation"),
   (1170, "function equation"), (1171, "function equation"), (1172, "function equation"),
   (1173, "function equation"), (1174, "function equation"), (1175, "function equation"),
   (1176, "function equation"), (1177, "function equation"), (1178, "function equation"),
   (1179, "function equation"), (1180, "function equation"), (1181, "function equation"),
   (1182, "function equation"), (1183, "function equation"), (1184, "function equation"),
   (1185, "function equation"), (1186, "function equation"), (1187, "function equation"),
   (1188, "function equation"), (1189, "function equation"), (1190, "function equation"),
   (1191, "function equation"), (1192, "function equation"), (1193, "function equation"),
   (1194, "function equation"), (1195, "function equation"), (1196, "function equation"),
   (1197, "function equation"), (1198, "function equation"), (1199, "function equation"),
   (1200, "function equation"), (1201, "function equation"), (1202, "function equation"),
   (1203, "function equation"), (1204, "function equation"), (1205, "function equation"),
   (1206, "function equation"), (1207, "function equation"), (1208, "function equation"),
   (1209, "function equation"), (1210, "function equation"), (1211, "function equation"),
   (1212, "function equation"), (1213, "function equation"), (1214, "function equation"),
   (1215, "function equation"), (1216, "function equation"), (1217, "function equation"),
   (1218, "function equation"), (1219, "function equation"), (1220, "function equation"),
   (1221, "function equation"), (1222, "function equation"), (1223, "function equation"),
   (1224, "function equation"), (1225, "function equation"), (1226, "function equation"),
   (1227, "function equation"), (1228, "function equation"), (1229, "function equation"),
   (1230, "function equation"), (1231, "function equation"), (1232, "function equation"),
   (1233, "function equation"), (1234, "function equation"), (1235, "function equation"),
   (1236, "function equation"), (1237, "function equation"), (1238, "function equation"),
   (1239, "function equation"), (1240, "function equation"), (1241, "function equation"),
   (1242, "function equation"), (1243, "function equation"), (1244, "function equation"),
   (1245, "function equation"), (1246, "function equation"), (1247, "function equation"),
   (1248, "function equation"), (1249, "function equation"), (1250, "function equation"),
   (1251, "function equation"), (1252, "function equation"), (1253, "function equation"),
   (1254, "function equation"), (1255, "function equation"), (1256, "function equation"),
   (1257, "function equation"), (1258, "function equation"), (1259, "function equation"),
   (1260, "function equation"), (1261, "function equation"), (1262, "function equation"),
   (1263, "function equation"), (1264, "function equation"), (1265, "function equation"),
   (1266, "function equation"), (1267, "function equation"), (1268, "function equation"),
   (1269, "function equation"), (1270, "function equation"), (1271, "function equation"),
   (1272, "function equation"), (1273, "function equation"), (1274, "function equation"),
   (1275, "function equation"), (1276, "function equation"), (1277, "function equation"),
   (1278, "function equation"), (1279, "function equation"), (1280, "function equation"),
   (1281, "function equation"), (1282, "function equation"), (1283, "function equation"),
   (1284, "function equation"), (1285, "function equation"), (1286, "function equation"),
   (1287, "function equation"), (1288, "function equation"), (1289, "function equation"),
   (1290, "function equation"), (1291, "function equation"), (1292, "function equation"),
   (1293, "function equation"), (1294, "function equation"), (1295, "function equation"),
   (1296, "function equation"), (1297, "function equation"), (1298, "function equation"),
   (1299, "function equation"), (1300, "function equation"), (1301, "function equation"),
   (1302, "function equation"), (1303, "function equation"), (1304, "function equation"),
   (1305, "function equation"), (1306, "function equation"), (1307, "function equation"),
   (1308, "function equation"), (1309, "function equation"), (1310, "function equation"),
   (1311, "function equation"), (1312, "function equation"), (1313, "function equation"),
   (1314, "function equation"), (1315, "function equation"), (1316, "function equation"),
   (1317, "function equation"), (1318, "function equation"), (1319, "function equation"),
   (1320, "function equation"), (1321, "function equation"), (1322, "function equation"),
   (1323, "function equation"), (1324, "function equation"), (1325, "function equation"),
   (1326, "function equation"), (1327, "function equation"), (1328, "function equation"),
   (1329, "function equation"), (1330, "function equation"), (1331, "function equation"),
   (1332, "function equation"), (1333, "function equation"), (1334, "function equation"),
   (1335, "function equation"), (1336, "function equation"), (1337, "function equation"),
   (1338, "function equation"), (1339, "function equation"), (1340, "function equation"),
   (1341, "function equation"), (1342, "function equation"), (1343, "function equation"),
   (1344, "function equation"), (1345, "function equation"), (1346, "function equation"),
   (1347, "function equation"), (1348, "function equation"), (1349, "function equation"),
   (1350, "function equation"), (1351, "function equation"), (1352, "function equation"),
   (1353, "function equation"), (1354, "function equation"), (1355, "function equation"),
   (1356, "function equation"), (1357, "function equation"), (1358, "function equation"),
   (1359, "function equation"), (1360, "function equation"), (1361, "function equation"),
   (1362, "function equation"), (1363, "function equation"), (1364, "function equation"),
   (1365, "function equation"), (1366, "function equation"), (1367, "function equation"),
   (1368, "function equation"), (1369, "function equation"), (1370, "function equation"),
   (1371, "function equation"), (1372, "function equation"), (1373, "function equation"),
   (1374, "function equation"), (1375, "function equation"), (1376, "function equation"),
   (1377, "function equation"), (1378, "function equation"), (1379, "function equation"),
   (1380, "function equation"), (1381, "function equation"), (1382, "function equation"),
   (1383, "function equation"), (1384, "function equation"), (1385, "function equation"),
   (1386, "function equation"), (1387, "function equation"), (1388, "function equation"),
   (1389, "function equation"), (1390, "function equation"), (1391, "function equation"),
   (1392, "function equation"), (1393, "function equation"), (1394, "function equation"),
   (1395, "function equation"), (1396, "function equation"), (1397, "function equation"),
   (1398, "function equation"), (1399, "function equation"), (1400, "function equation"),
   (1401, "function equation"), (1402, "function equation"), (1403, "function equation"),
   (1404, "function equation"), (1405, "function equation"), (1406, "function equation"),
   (1407, "function equation"), (1408, "function equation"), (1409, "function equation"),
   (1410, "function equation"), (1411, "function equation"), (1412, "function equation"),
   (1413, "function equation"), (1414, "function equation"), (1415, "function equation"),
   (1416, "function equation"), (1417, "function equation"), (1418, "function equation"),
   (1419, "function equation"), (1420, "function equation"), (1421, "function equation"),
   (1422, "function equation"), (1423, "function equation"), (1424, "function equation"),
   (1425, "function equation"), (1426, "function equation"), (1427, "function equation"),
   (1428, "function equation"), (1429, "function equation"), (1430, "function equation"),
   (1431, "function equation"), (1432, "function equation"), (1433, "function equation"),
   (1434, "function equation"), (1435, "function equation"), (1436, "function equation"),
   (1437, "function equation"), (1438, "function equation"), (1439, "function equation"),
   (1440, "function equation"), (1441, "function equation"), (1442, "function equation"),
   (1443, "function equation"), (1444, "function equation"), (1445, "function equation"),
   (1446, "function equation"), (1447, "function equation"), (1448, "function equation"),
   (1449, "function equation"), (1450, "function equation"), (1451, "function equation"),
   (1452, "function equation"), (1453, "function equation"), (1454, "function equation"),
   (1455, "function equation"), (1456, "function equation"), (1457, "function equation"),
   (1458, "function equation"), (1459, "function equation"), (1460, "function equation"),
   (1461, "function equation"), (1462, "function equation"), (1463, "function equation"),
   (1464, "function equation"), (1465, "function equation"), (1466, "function equation"),
   (1467, "function equation"), (1468, "function equation"), (1469, "function equation"),
   (1470, "function equation"), (1471, "function equation"), (1472, "function equation"),
   (1473, "function equation"), (1474, "function equation"), (1475, "function equation"),
   (1476, "function equation"), (1477, "function equation"), (1478, "function equation"),
   (1479, "function equation"), (1480, "function equation"), (1481, "function equation"),
   (1508, "no direction"), (1509, "no direction"), (1510, "no direction"), (1511, "no direction"),
   (1512, "no direction"), (1513, "no direction"), (1514, "no direction"), (1515, "no direction"),
   (1516, "no direction"), (1517, "no direction"), (1518, "no direction"), (1519, "no direction"),
   (1520, "no direction"), (1521, "no direction"), (1522, "no direction"), (1523, "no direction"),
   (1524, "no direction"), (1525, "no direction"), (1526, "no direction"), (1527, "no direction"),
   (1528, "no direction"), (1529, "no direction"), (1530, "no direction"), (1531, "no direction"),
   (1532, "no direction"), (1533, "no direction"), (1534, "no direction"), (1535, "no direction"),
   (1536, "no direction"), (1537, "no direction"), (1538, "no direction"), (1539, "no direction"),
   (1540, "no direction"), (1541, "no direction"), (1542, "no direction"), (1543, "no direction"),
   (1544, "no direction"), (1545, "no direction"), (1546, "no direction"), (1547, "no direction"),
   (1548, "no direction"), (1549, "no direction"), (1550, "no direction"), (1551, "no direction"),
   (1552, "no direction"), (1553, "no direction"), (1554, "no direction"), (1555, "no direction"),
   (1556, "no direction"), (1557, "no direction"), (1558, "no direction"), (1559, "no direction"),
   (1560, "no direction"), (1561, "no direction"), (1562, "no direction"), (1563, "no direction"),
   (1564, "no direction"), (1565, "no direction"), (1566, "no direction"), (1567, "no direction"),
   (1568, "no direction"), (1569, "no direction"), (1570, "no direction"), (1571, "no direction"),
   (1572, "no direction"), (1573, "no direction"), (1574, "no direction"), (1575, "no direction"),
   (1576, "no direction"), (1577, "no direction"), (1578, "no direction"), (1579, "no direction"),
   (1580, "no direction"), (1581, "no direction"), (1582, "no direction"), (1583, "no direction"),
   (1584, "no direction"), (1585, "no direction"), (1586, "no direction"), (1587, "no direction"),
   (1588, "no direction"), (1589, "no direction"), (1590, "no direction"), (1591, "no direction"),
   (1592, "no direction"), (1593, "no direction"), (1594, "no direction"), (1595, "no direction"),
   (1596, "no direction"), (1597, "no direction"), (1598, "no direction"), (1599, "no direction"),
   (1600, "no direction"), (1601, "no direction"), (1602, "no direction"), (1603, "no direction"),
   (1604, "no direction"), (1605, "no direction"), (1606, "no direction"), (1607, "no direction"),
   (1608, "no direction"), (1609, "no direction"), (1610, "no direction"), (1611, "no direction"),
   (1612, "no direction"), (1613, "no direction"), (1614, "no direction"), (1615, "no direction"),
   (1616, "no direction"), (1617, "no direction"), (1618, "no direction"), (1619, "no direction"),
   (1620, "no direction"), (1621, "no direction"), (1622, "no direction"), (1623, "no direction"),
   (1624, "no direction"), (1625, "no direction"), (1626, "no direction"), (1627, "no direction"),
   (1628, "no direction"), (1629, "no direction"), (1630, "no direction"), (1631, "no direction"),
   (1632, "no direction"), (1633, "no direction"), (1634, "no direction"), (1635, "no direction"),
   (1636, "no direction"), (1637, "no direction"), (1638, "no direction"), (1639, "no direction"),
   (1640, "no direction"), (1641, "no direction"), (1642, "no direction"), (1643, "no direction"),
   (1644, "no direction"), (1645, "no direction"), (1646, "no direction"), (1647, "no direction"),
   (1648, "no direction"), (1649, "no direction"), (1650, "no direction"), (1651, "no direction"),
   (1652, "no direction"), (1653, "no direction"), (1654, "no direction"), (1655, "no direction"),
   (1656, "no direction"), (1657, "no direction"), (1658, "no direction"), (1659, "no direction"),
   (1660, "no direction"), (1661, "no direction"), (1662, "no direction"), (1663, "no direction"),
   (1664, "no direction"), (1665, "no direction"), (1666, "no direction"), (1667, "no direction"),
   (1668, "no direction"), (1669, "no direction"), (1670, "no direction"), (1671, "no direction"),
   (1672, "no direction"), (1673, "no direction"), (1674, "no direction"), (1675, "no direction"),
   (1676, "no direction"), (1677, "no direction"), (1678, "no direction"), (1679, "no direction"),
   (1680, "no direction"), (1681, "no direction"), (1682, "no direction"), (1683, "no direction"),
   (1684, "no direction"), (1685, "no direction"), (1686, "no direction"), (1687, "no direction"),
   (1688, "no direction"), (1689, "no direction"), (1690, "no direction"), (1691, "no direction"),
   (1692, "no direction"), (1693, "no direction"), (1694, "no direction"), (1695, "no direction"),
   (1696, "no direction"), (1710, "set-variable lemma")]

/-- The sentences of a class with a theorem in the tie that no theorem of this file holds of: the
tie's remainder on this text. -/
def uncovered : List (Nat × String) :=
  []

/-- Each listed sentence is in its class in the account. -/
theorem lists_in_account : (unmapped ++ uncovered).all (fun ic => (classOf ic.2).contains ic.1) = true := by
  decide +kernel

/-! ## Γ's symbol names, as a literal -/

/-- Γ's symbol names (`c.symName` of each of `kernelSyms c`, in its order), each as its code
(`KoreAML.Distinct.strCode`), written out. -/
def gSymCodes : List Nat :=
  [6197441387, 6097760100, 121428802336216206740958059929080174872702535030001388262469165644,
   723510575035956901380327913738874742029515191727491810128586290066398996996788868375116,
   100443551098051763654892637080606156284492, 440560881882751606213861964,
   598473920646836122746414403872685673534140921181473059287884364,
   100443551098051764863818456695235330990668, 440560881883033081190572620,
   598473920646836122746414403872685673535349847001087688462590540,
   100443551098051766072744276309864505696844, 440560881883314556167283276,
   598473920646836122746414403872685673536558772820702317637296716,
   100443551098051767281670095924493680403020, 440560881883596031143993932,
   598473920646836122746414403872685673537767698640316946812002892,
   100443551098051768490595915539122855109196, 440560881883877506120704588,
   598473920646836122746414403872685673538976624459931575986709068,
   100443551098051769699521735153752029815372, 440560881884158981097415244,
   598473920646836122746414403872685673540185550279546205161415244,
   100443551098051770908447554768381204521548, 440560881884440456074125900,
   598473920646836122746414403872685673541394476099160834336121420,
   100443551098051772117373374383010379227724, 440560881884721931050836556,
   598473920646836122746414403872685673542603401918775463510827596,
   100443551098051773326299193997639553933900, 440560881885003406027547212,
   598473920646836122746414403872685673543812327738390092685533772,
   25713549081101251126004442791106126812045900, 112783585761907238672947503692,
   153209323685590047423082087391407532424370427750155574128501613132,
   25713549081101251435489452612451195536826956, 112783585761979296266985431628,
   153209323685590047423082087391407532424679912759976919197226394188,
   25713549081101251744974462433796264261608012, 112783585762051353861023359564,
   153209323685590047423082087391407532424989397769798264265951175244,
   25713549081101252054459472255141332986389068, 112783585762123411455061287500,
   153209323685590047423082087391407532425298882779619609334675956300,
   25713549081101252363944482076486401711170124, 112783585762195469049099215436,
   153209323685590047423082087391407532425608367789440954403400737356,
   25713549081101252673429491897831470435951180, 112783585762267526643137143372,
   153209323685590047423082087391407532425917852799262299472125518412,
   25713549081101252982914501719176539160732236, 112783585762339584237175071308,
   153209323685590047423082087391407532426227337809083644540850299468,
   25713549081101253292399511540521607885513292, 112783585762411641831212999244,
   153209323685590047423082087391407532426536822818904989609575080524,
   25713549081101253601884521361866676610294348, 112783585762483699425250927180,
   153209323685590047423082087391407532426846307828726334678299861580,
   25713549081101253911369531183211745335075404, 112783585762555757019288855116,
   153209323685590047423082087391407532427155792838547679747024642636,
   25713549081101251127213368610720755986752076, 112783585761907520147924214348,
   153209323685590047423082087391407532424371636675975188757676319308,
   25713549081101251436698378432065824711533132, 112783585761979577741962142284,
   153209323685590047423082087391407532424681121685796533826401100364,
   25713549081101251746183388253410893436314188, 112783585762051635336000070220,
   153209323685590047423082087391407532424990606695617878895125881420,
   25713549081101252055668398074755962161095244, 112783585762123692930037998156,
   153209323685590047423082087391407532425300091705439223963850662476,
   25713549081101252365153407896101030885876300, 112783585762195750524075926092,
   153209323685590047423082087391407532425609576715260569032575443532,
   25713549081101252674638417717446099610657356, 112783585762267808118113854028,
   153209323685590047423082087391407532425919061725081914101300224588,
   25713549081101252984123427538791168335438412, 112783585762339865712151781964,
   153209323685590047423082087391407532426228546734903259170025005644,
   25713549081101253293608437360136237060219468, 112783585762411923306189709900,
   153209323685590047423082087391407532426538031744724604238749786700,
   25713549081101253603093447181481305785000524, 112783585762483980900227637836,
   153209323685590047423082087391407532426847516754545949307474567756,
   25713549081101253912578457002826374509781580, 112783585762556038494265565772,
   153209323685590047423082087391407532427157001764367294376199348812,
   25713549081101251128422294430335385161458252, 112783585761907801622900925004,
   153209323685590047423082087391407532424372845601794803386851025484,
   25713549081101251437907304251680453886239308, 112783585761979859216938852940,
   153209323685590047423082087391407532424682330611616148455575806540,
   25713549081101251747392314073025522611020364, 112783585762051916810976780876,
   153209323685590047423082087391407532424991815621437493524300587596,
   25713549081101252056877323894370591335801420, 112783585762123974405014708812,
   153209323685590047423082087391407532425301300631258838593025368652,
   25713549081101252366362333715715660060582476, 112783585762196031999052636748,
   153209323685590047423082087391407532425610785641080183661750149708,
   25713549081101252675847343537060728785363532, 112783585762268089593090564684,
   153209323685590047423082087391407532425920270650901528730474930764,
   25713549081101252985332353358405797510144588, 112783585762340147187128492620,
   153209323685590047423082087391407532426229755660722873799199711820,
   25713549081101253294817363179750866234925644, 112783585762412204781166420556,
   153209323685590047423082087391407532426539240670544218867924492876,
   25713549081101253604302373001095934959706700, 112783585762484262375204348492,
   153209323685590047423082087391407532426848725680365563936649273932,
   25713549081101253913787382822441003684487756, 112783585762556319969242276428,
   153209323685590047423082087391407532427158210690186909005374054988,
   25713549081101251129631220249950014336164428, 112783585761908083097877635660,
   153209323685590047423082087391407532424374054527614418016025731660,
   25713549081101251439116230071295083060945484, 112783585761980140691915563596,
   153209323685590047423082087391407532424683539537435763084750512716,
   25713549081101251748601239892640151785726540, 112783585762052198285953491532,
   153209323685590047423082087391407532424993024547257108153475293772,
   25713549081101252058086249713985220510507596, 112783585762124255879991419468,
   153209323685590047423082087391407532425302509557078453222200074828,
   25713549081101252367571259535330289235288652, 112783585762196313474029347404,
   153209323685590047423082087391407532425611994566899798290924855884,
   25713549081101252677056269356675357960069708, 112783585762268371068067275340,
   153209323685590047423082087391407532425921479576721143359649636940,
   25713549081101252986541279178020426684850764, 112783585762340428662105203276,
   153209323685590047423082087391407532426230964586542488428374417996,
   25713549081101253296026288999365495409631820, 112783585762412486256143131212,
   153209323685590047423082087391407532426540449596363833497099199052,
   25713549081101253605511298820710564134412876, 112783585762484543850181059148,
   153209323685590047423082087391407532426849934606185178565823980108,
   25713549081101253914996308642055632859193932, 112783585762556601444218987084,
   153209323685590047423082087391407532427159419616006523634548761164,
   25713549081101251130840146069564643510870604, 112783585761908364572854346316,
   153209323685590047423082087391407532424375263453434032645200437836,
   25713549081101251440325155890909712235651660, 112783585761980422166892274252,
   153209323685590047423082087391407532424684748463255377713925218892,
   25713549081101251749810165712254780960432716, 112783585762052479760930202188,
   153209323685590047423082087391407532424994233473076722782649999948,
   25713549081101252059295175533599849685213772, 112783585762124537354968130124,
   153209323685590047423082087391407532425303718482898067851374781004,
   25713549081101252368780185354944918409994828, 112783585762196594949006058060,
   153209323685590047423082087391407532425613203492719412920099562060,
   25713549081101252678265195176289987134775884, 112783585762268652543043985996,
   153209323685590047423082087391407532425922688502540757988824343116,
   25713549081101252987750204997635055859556940, 112783585762340710137081913932,
   153209323685590047423082087391407532426232173512362103057549124172,
   25713549081101253297235214818980124584337996, 112783585762412767731119841868,
   153209323685590047423082087391407532426541658522183448126273905228,
   25713549081101253606720224640325193309119052, 112783585762484825325157769804,
   153209323685590047423082087391407532426851143532004793194998686284,
   25713549081101253916205234461670262033900108, 112783585762556882919195697740,
   153209323685590047423082087391407532427160628541826138263723467340,
   25713549081101251132049071889179272685576780, 112783585761908646047831056972,
   153209323685590047423082087391407532424376472379253647274375144012,
   25713549081101251441534081710524341410357836, 112783585761980703641868984908,
   153209323685590047423082087391407532424685957389074992343099925068,
   25713549081101251751019091531869410135138892, 112783585762052761235906912844,
   153209323685590047423082087391407532424995442398896337411824706124,
   25713549081101252060504101353214478859919948, 112783585762124818829944840780,
   153209323685590047423082087391407532425304927408717682480549487180,
   392357621476764974567819039771953226316, 1720940944883274725745228,
   521532734826497016649662551218561087122972325775062832838783014564719780428,
   2287522883088336244638867367476247085107051579558290160116300, 364434038743628,
   1725535266710405929263692, 1923124077015793602518953244536627788, 26544582836783702604,
   26833945709912023628, 6870505057665443193420, 6722644552554359054924, 26836467989586141772,
   532605425241745453507524652420459454565755214651980,
   10040726237058829336038956037158422865491579578865221826606303537816140,
   440560881882751623309845068, 7553954507151666951185838243603020,
   8305494079247579015089250417180600286820721228, 440560881883033098286555724,
   7553954507151666951467313220313676, 8305494079247579015089250417180881761797431884,
   440560881883314573263266380, 7553954507151666951748788197024332,
   8305494079247579015089250417181163236774142540, 440560881883596048239977036,
   7553954507151666952030263173734988, 8305494079247579015089250417181444711750853196,
   440560881883877523216687692, 7553954507151666952311738150445644,
   8305494079247579015089250417181726186727563852, 440560881884158998193398348,
   7553954507151666952593213127156300, 8305494079247579015089250417182007661704274508,
   440560881884440473170109004, 7553954507151666952874688103866956,
   8305494079247579015089250417182289136680985164, 440560881884721948146819660,
   7553954507151666953156163080577612, 8305494079247579015089250417182570611657695820,
   440560881885003423123530316, 7553954507151666953437638057288268,
   8305494079247579015089250417182852086634406476, 112783585761907238690043486796,
   1933812353830826739426397713085522508, 2126206484287380227862848106798156496548827783756,
   112783585761979296284081414732, 1933812353830826739498455307123450444,
   2126206484287380227862848106798228554142865711692, 112783585762051353878119342668,
   1933812353830826739570512901161378380, 2126206484287380227862848106798300611736903639628,
   112783585762123411472157270604, 1933812353830826739642570495199306316,
   2126206484287380227862848106798372669330941567564, 112783585762195469066195198540,
   1933812353830826739714628089237234252, 2126206484287380227862848106798444726924979495500,
   112783585762267526660233126476, 1933812353830826739786685683275162188,
   2126206484287380227862848106798516784519017423436, 112783585762339584254271054412,
   1933812353830826739858743277313090124, 2126206484287380227862848106798588842113055351372,
   112783585762411641848308982348, 1933812353830826739930800871351018060,
   2126206484287380227862848106798660899707093279308, 112783585762483699442346910284,
   1933812353830826740002858465388945996, 2126206484287380227862848106798732957301131207244,
   112783585762555757036384838220, 1933812353830826740074916059426873932,
   2126206484287380227862848106798805014895169135180, 112783585761907520165020197452,
   1933812353830826739426679188062233164, 2126206484287380227862848106798156778023804494412,
   112783585761979577759058125388, 1933812353830826739498736782100161100,
   2126206484287380227862848106798228835617842422348, 112783585762051635353096053324,
   1933812353830826739570794376138089036, 2126206484287380227862848106798300893211880350284,
   112783585762123692947133981260, 1933812353830826739642851970176016972,
   2126206484287380227862848106798372950805918278220, 112783585762195750541171909196,
   1933812353830826739714909564213944908, 2126206484287380227862848106798445008399956206156,
   112783585762267808135209837132, 1933812353830826739786967158251872844,
   2126206484287380227862848106798517065993994134092, 112783585762339865729247765068,
   1933812353830826739859024752289800780, 2126206484287380227862848106798589123588032062028,
   112783585762411923323285693004, 1933812353830826739931082346327728716,
   2126206484287380227862848106798661181182069989964, 112783585762483980917323620940,
   1933812353830826740003139940365656652, 2126206484287380227862848106798733238776107917900,
   112783585762556038511361548876, 1933812353830826740075197534403584588,
   2126206484287380227862848106798805296370145845836, 112783585761907801639996908108,
   1933812353830826739426960663038943820, 2126206484287380227862848106798157059498781205068,
   112783585761979859234034836044, 1933812353830826739499018257076871756,
   2126206484287380227862848106798229117092819133004, 112783585762051916828072763980,
   1933812353830826739571075851114799692, 2126206484287380227862848106798301174686857060940,
   112783585762123974422110691916, 1933812353830826739643133445152727628,
   2126206484287380227862848106798373232280894988876, 112783585762196032016148619852,
   1933812353830826739715191039190655564, 2126206484287380227862848106798445289874932916812,
   112783585762268089610186547788, 1933812353830826739787248633228583500,
   2126206484287380227862848106798517347468970844748, 112783585762340147204224475724,
   1933812353830826739859306227266511436, 2126206484287380227862848106798589405063008772684,
   112783585762412204798262403660, 1933812353830826739931363821304439372,
   2126206484287380227862848106798661462657046700620, 112783585762484262392300331596,
   1933812353830826740003421415342367308, 2126206484287380227862848106798733520251084628556,
   112783585762556319986338259532, 1933812353830826740075479009380295244,
   2126206484287380227862848106798805577845122556492, 112783585761908083114973618764,
   1933812353830826739427242138015654476, 2126206484287380227862848106798157340973757915724,
   112783585761980140709011546700, 1933812353830826739499299732053582412,
   2126206484287380227862848106798229398567795843660, 112783585762052198303049474636,
   1933812353830826739571357326091510348, 2126206484287380227862848106798301456161833771596,
   112783585762124255897087402572, 1933812353830826739643414920129438284,
   2126206484287380227862848106798373513755871699532, 112783585762196313491125330508,
   1933812353830826739715472514167366220, 2126206484287380227862848106798445571349909627468,
   112783585762268371085163258444, 1933812353830826739787530108205294156,
   2126206484287380227862848106798517628943947555404, 112783585762340428679201186380,
   1933812353830826739859587702243222092, 2126206484287380227862848106798589686537985483340,
   112783585762412486273239114316, 1933812353830826739931645296281150028,
   2126206484287380227862848106798661744132023411276, 112783585762484543867277042252,
   1933812353830826740003702890319077964, 2126206484287380227862848106798733801726061339212,
   112783585762556601461314970188, 1933812353830826740075760484357005900,
   2126206484287380227862848106798805859320099267148, 112783585761908364589950329420,
   1933812353830826739427523612992365132, 2126206484287380227862848106798157622448734626380,
   112783585761980422183988257356, 1933812353830826739499581207030293068,
   2126206484287380227862848106798229680042772554316, 112783585762052479778026185292,
   1933812353830826739571638801068221004, 2126206484287380227862848106798301737636810482252,
   112783585762124537372064113228, 1933812353830826739643696395106148940,
   2126206484287380227862848106798373795230848410188, 112783585762196594966102041164,
   1933812353830826739715753989144076876, 2126206484287380227862848106798445852824886338124,
   112783585762268652560139969100, 1933812353830826739787811583182004812,
   2126206484287380227862848106798517910418924266060, 112783585762340710154177897036,
   1933812353830826739859869177219932748, 2126206484287380227862848106798589968012962193996,
   112783585762412767748215824972, 1933812353830826739931926771257860684,
   2126206484287380227862848106798662025607000121932, 112783585762484825342253752908,
   1933812353830826740003984365295788620, 2126206484287380227862848106798734083201038049868,
   112783585762556882936291680844, 1933812353830826740076041959333716556,
   2126206484287380227862848106798806140795075977804, 112783585761908646064927040076,
   1933812353830826739427805087969075788, 2126206484287380227862848106798157903923711337036,
   112783585761980703658964968012, 1933812353830826739499862682007003724,
   2126206484287380227862848106798229961517749264972, 112783585762052761253002895948,
   1933812353830826739571920276044931660, 2126206484287380227862848106798302019111787192908,
   112783585762124818847040823884, 1933812353830826739643977870082859596,
   2126206484287380227862848106798374076705825120844, 1720940944883291821728332,
   29507634793561199056862973813324, 2287522883088336244638867367476247085107051579558307256099404,
   39222374256998602510383582347347576723698573932127104238925854302796,
   392721409877693815432988761667004031564, 110541249699099855892391312445803995868708249499624012,
   474771052316603721696133595434940758308856902371353117286228556,
   431801756637108812079653581170041260959453743440460,
   1854574423111733287875521810721331632085176143320548117340748,
   110541249699099855892391316779911673616259842661179980,
   474771052316603721696133602081102924831589231873303763678421580,
   121541389393050552754210176289927329604225962435654588342054183500,
   522016292553553413754055433475632494852177869876792572698254621020567396940,
   110541249699099866520250115792059833262706237461258828,
   6588771921342603356853161313397830312182702668,
   110541249699099866520250115458434141321163763532718668,
   110541249699099866520250112385306928928913444267909708,
   110541249699099866520250110836639842096961162824147532,
   431801756637108853594751451957700876051267474711116,
   431801756637108853594745888523580307873632283812428,
   359818203948122867293303604482612618905088028486620872813118667338780911453577053668790488270385212089664343204673559946156014899634221156181428150549519669368113776173015628,
   359818203948122867293303604482612618905088028486620872813118667338780911453577053668790488270385212089664343204673559946156014899634221156181428150549519669368124736929555020,
   110541249699099866520250094088062832357774255480136268,
   474771052316603767342439569020479967466498625674917660236472908,
   110541249699099866520250094088039220525359907254067788,
   474771052316603767342439569020479967466475013842503312010404428,
   474771052316603767342439569020479989159638703121547517066240588,
   2039126142787318218526170781799296293077820574614511115498546619212390988,
   4130510410781641971243815729516411916268814686839138853190129920375841703014865331853643666213555791693836718933537081955189229642316,
   3756677334223824774420623479742436680925324881010150535360749296241214041619179286744396004826574683887559779081744310860,
   474771052316603767342439475849051375238274334989369150876181068,
   474771052316603767342439475849152787286316205173903235358679628,
   1057410665160100344638416826756201450564816559830819546416673259616215475971805524954532778550670282673622200046985492962238126990582348,
   2039126142787794885943691446649778161763015347094001243221605056999350860,
   34463737067054453708261914389949095460273400893812449602330655995567421060377131071393750659243889322969411998734251810620725311657644544534412489999194821798760707264100949770510837028613207476711485456178392284861963057259084,
   41664101580771881637672447403171598916658895240499230309182649367834624854943476625330656820841565728441732337184554044091862969257728010814078548034046866468247489739193380207944483526190065909085766908236816448398177741472407404255045717995931066956,
   110541249699099866520250094124496682983108737814520396,
   7244431340280205256563526134932324411981019876294319170124,
   31114595684620929053107634095961031260542442552826855547696524845644,
   114008113768501626313175229004, 7244431340280339855840920836210215346772346621796345995852,
   25737390317744543109070370697722766016930380, 31138688288827425678961365311950143168995916,
   34188719201792904902010916185151803341388823883782707842803890857426458164093516,
   32097277065817937160513244483529207498695244,
   153206209948795800229742253919078430887182629684412494733283975756,
   355904663881745816747611301990166375698979510387134345344343749986365654080402482007456946952727689470058293365614080633607305563860212109481691584624919825328583544178238028,
   1739625776869486160011852,
   83768830100704611514832748496617513954056810367044455537429299529696898644046902876611646871845298876649924574360283009562196900526747541308807922060571730735030860,
   865156312811772925346444298571725572173587415257557439995249195936431637760265223408137719226262694676963025484,
   115250917845264362322644460108, 1725535266755425407361612,
   25737390317744544351874447460458775486161484,
   1057311282280751701680793791927645271583425324347419432914207084811285018187939049314840122085741484993525676331988496407321326394303052,
   1405407756666823019580439434632103007478270112683483554017731168962547490693617006363443128355357986672756190615174023281948131704666513270370743972906185632929622616990284,
   133714876552366999791601052533520075769802662930571852, 7431693075409800328385312185934412,
   1162526049046439129347931537318160701373401574240627691793327617662387934523617425196667985861987969948166201381799712974285593555322550745305997900,
   874587394136219348471392225015801214673787687036255140038605470909367223159335324207963408161392285885162873420,
   6588771921342603358439418382093192748398830156, 29508594528274225342887907582540,
   441737028289404391400432204, 450265419456077294388142668,
   494999328626962676979381452409257353804, 31134281882478915100800596151513682761507404,
   431801756637108853698685808874244120968604796346956, 450265419455240514550129228,
   494999572015877920799426539776272785996,
   1378991927647055423374985896269032264775223336800339596596997216873938562780913148762825711625103197086527165603217442539902841634848728502664237563438460518378328558428748,
   8024645462318859050392881966990660357767370346998469150762286569333359179493691609626750401997287840900010690862031575574599564214682119451309734732514649156696743344477638210712686056928724793712138991966974693368396,
   2678924720470327893023682407866081270739668438286102840877359916391689023491043433377163414732100944543106312628500490569110169870961588469467488189012718276681604589733144837901202543083006968626732066118646377981270550458606654528858024630856793635709516,
   1278158757846668955099257422144909981145900669517271225144376611645358319477970077858247181723332281492142092861428696163689090037556957865412625350625061528140,
   76184198728005227750495518573815225431078712315396739551089800098261733023999338022365998132427470772990113071288388738852089049697447033206966011585100,
   1278158757846668955099257422144909981145900669517271225144376611645358319477970077858247181723332281492142092861428696163689090037556624239720683808151132987980,
   1278158757846668955099257422144909981145900669517271225144376611645358319477970077858247181723332281492142092861428696163689090037553551112508291557831868179020,
   1278158757846668955099257422144909981145900669517271225144376611645358319477970077858247181723332281492142092861428696163689090037552002445421459605550424416844,
   223885238066731617274542746151453078888082066993629414087115869494980692679650728461091877236286967684524394963532,
   1057268144255624594408875507514855926914347676806537327832554850237804243434800670817832831487709743258313437446528910093646811603165772,
   69289125101936613419180065260493598026258689347193230316834314665184738897743096762717492444378545734176829436495718651897169062198963364428,
   270660644929439896168672129923803117290073005262473555925134041660877886319308971729365204860853694274128239986311400983971621159184392780,
   69289125101936613419180065260493598026258689347193230316834314665184738897743096762717492444378545734176829436495718651896087923436492186188,
   270660644929439896168672129923803117290073005262473555925134041660877886319308971729365204860853694274128239986311400983973882906410771020,
   21443945562685259940194543210928338054240703047035875070054900476153868762879466028686577059614369870658392253138452620204192556828837903755133119025538586977814471244,
   4992807647838550605856474305253554613851174490301840722108003794251444927155847202215012409634508628085812612701778444509066770955842588235772305959486775884,
   21443945562685259940194543210928338054240703047035875070054900476153868762879466028686577059614369870658392253138452620204192556828837903755133095413706172629588402764,
   4992807647838550605856474305253554613851174490301840722108003794251444927155847202215012409634508628085812612701778444509066770955842564623939891611260707404,
   31114595684620944477773074767204953812994952830104929799984361792076,
   92101044888937509384394478968596041742596093699066633164627506469615694200443285383151846305227560966125544715169407363822515873666480266392078403342875413693054687401474810444,
   246164422541769359821657535490106244337092768812147572204751573734553143573700865198361862257942873870445342474855810488623692,
   270660644929439896168672129905143206654258852292163223077172895998576214226697672118750400299909468034512817670727074940791940450259591756,
   4540932102680517897039384756913686315119381720433514137833175150655572754422741862237528618774727604144335608364764425477283546851096599945044556,
   76184198728005227750495518573848408665001932910164680329480951468381085704665295535001260943365260355892013678027059581411170348044012501572579886916172,
   525874894211646327335539465178666617740988172815004807542197659684655805545500813258062929485749857376600460735893807354050688610506159636946046706392981026476727214222179737569810980270095677563931929441860735855382782540,
   31344586265781302889319626401583350762187729645859189624689548505163999791233081529618725700930054264776811976508313417907481000454955612797240225215425049715457255408958549614373425198225300647987292151896855044684,
   1545407418462645795614487021051740198834264410341812772287597428945449495164986181895779889665482646909867941944229663571760569292689550530219717978644956240952043741618521239460799052,
   1545407418462645795614487021051740198834264410341812772287597428945449495164986181895779889665482646909867941944229663571760569292689550530219717978644956240952043741618510278704259660,
   97744700096415190049420025006180177383269303311070178874375791931710490110710108590110618807452697315279101908165710795667685449632912627701998900843808412499597187397931462830420776477260,
   315830159763924609908200062846839709210420134331616959945285715341710654491762327489756176525104137857053636274003949593085632018113046676778737094595730727526988,
   287245856965386892541755571843932292913832620189729786893881933194016396093286246004714645573680298054617775300361199327276728649817002408472128283212,
   41664101580771881637672447403171598916658895175287767545764719303340507588494951948594266665138409099753343749175251417307002354088789689031074735404176063559237732627672131136085032222707419020792286665551955231441212062725770565799139914756788085324,
   635743737499570947840456229412010895536708534729752849735059589881431508606639103938840407501241113629831330509169214861349486263364385470240383653539880954425538962158997147703866720097397873599577836673490000698180322803143026080710399298921036,
   162750396799890162647156794729474789257397384890816729532175255009646466203299610608343144320317725089236820610347319004505468483421282680381538215306209524332937974312703269812189880344933855641491926188413440178734162637604614676661862220625109580,
   9700679588311324277350711508361982658946358256984754176865533292868522775369859374066778678912980859830189979693133771688071994985418479465337885338438124914940474886459307063352458497579923608391995798850860606356524510012731705714065302092,
   2483373974607699015001782146140667560690267713788097069277576522974341830494683999761095341801723100116528634801442245552146430716267130743126498646640159978224761570933582608218229375380460443748350924505820315227270274563259316662800818659916,
   315830159763924609908200062846751033551577114365542258520898468071364865534941957284073733604562865385773205920799463933599909706481627148139049036298236900172364,
   4819185787413400419741822248029170367590639256769057616352626271693582984798619499050234627153078275406702213653624719132776368493810283110075344648902828620,
   111358340382783548567571311323574351269602588539835479811656358589787696727424310411795614862108655361593036302583181018173201028066871339457126184697122357553211603968330535378825337610184060088115788,
   929140513278490685034793801323958888658952632714447772656861063235971372053944493545120310243182938166663128127257159445026367299431066027292754951500640062433713417112591924111635241663095100524197974552972612069709652759921278501882890859047167944829158871607476118159077451331514861812998732,
   11318063036038816616853562875845436906649041088530840937320202021670123186222903423159217928070420622786993286898071687376218397459565238167244120376670738584320823388113088060051496766424182974688369721250721066056016027722245921151967446445257615874292265945686604,
   33260797902785442906837272006560232390804317436275313278985696640800038241167547777640894630873406015366207412622579875164156845329222149641346480609132954052847621276002931319217580617685957580881463708037879275063189047108172,
   172699936462994638318688398374106398111710221687787489888308746668550463656965689440295683716894845928756611433381220815677160605767291842151552129770976846074231313905534180603813122046267440409673610248576676422973877376132902848972827321272130147058770010700,
   6405796665518665895078790758805024104989937061794295242711106107447855264967671591613710615376127360523275191107834701789163414844083755337056843943165410479126132928798528969657480515110593100,
   27512687183228520896913973652294602571423450089504829146812583107474400388377563983249154958248501752578268392616300053558369553955020668257524601628871120726262431573553116319119066550946272615747838540,
   1491465760748522797384949112032778585560139515854952680578247203363071955965755412265125339705526679876091701702176290980811094596070180492721694508373134393700120446413909379666174540,
   6405796665518665895078790758805024104989937061794295242711106107447855264967671591613710615376127360523275191107834701789163414844083755337056843943165410479126132907105388892210850658280825420,
   1491465760748522797384949112032778585560139515854952680578247203363071955965755412265125339705526679876091701702176290980811094596070180492721694508373134393700096834581495031440106060,
   6405796665518665895078790758805024104989937061794295242711106107447855264967671591613710615376127360523275191107834701789163414844083755337056843943165410479126132907105365280378436310054756940,
   297634642349538514324704175597681126997417192040467897483678914397804822253879923383284425526288781339367909316149170765556657606240325285563616485964,
   4993480683780955155144656090104225366759099672976410657149537621497481428794950312664813596490460562907344718065446926154629404030451833609343052639470641740,
   320227140582394429650577826068134584819209220144992056842381266941485280356198748821957923680241776536584094908672591862986651273602180594709305959133662830944844,
   11696541816650300215214752022706065902162560558025510489619272010858215166000075377413653796953486398106538800927777084793359887285264920862265994324226327382707890228433887428609924212201728456668695678004302745462076520445891895160817714181907413156446693363573324,
   122439790100708214411404790631184963914795818913886888428922381360675449191703035839243683263963507993244905122813426090698076331963506375559030956621400425515580866300902640141400271638553146126718697472342647372,
   1278331055047924519717040655700741577037933615462247725988960598406055637978873155215519264257846889111720571376383090932535340367171252136357165535372170256972,
   9700679588311324277350783209123555318605828852232017064918210363766643759269813918451353040324558975985772498112854396559297017648722709421444388381710995210004152249431425241840888907369346037555202753395004199702377705042793311571733668428,
   10636383194724617320682002740755429133037484763228580305584890747238064550164143344004462867926427706827685326293555385720796894009982346823080081317994480209938054014291325307421768348805084196707916965019373245345350299653643231108507548794998647185996,
   845048374029366355020829968355015410437994222864502444056095737688456781153288078867242854765554579545105385613859045924013463965181541726635743769074428757650329258427858111893539503563264292181918633005603363300904511367314619537181788497518527172612447195160290009371356364038732,
   635743737499570947840460928393121321360151599659877470366479834399810765407506524959627872850710297050203586436324025732910089348626691484643779436983811782082832121818737884649284495433357461917217767646494995231695025280045464842206070184895052,
   2483373974607699015001800501535630161563092186171396368619061853124260802373072363123546378323087097852357759516890725519180036518073013611889763425718014773761062975854444861911267560286552585614131904869121075123808692500140551293536217883212,
   326343745222657344184731151930983217933635095887432070723588505346266590950512821261967102701206323662224861815322190921423677945675758218110651947447461673198156,
   19451603008667072307153412814970038597441597822186483696842741046342379591087467073357706247040630186662142679419603193989994523250703351856787258499424844,
   91857598086215731215573718145170156430937517931518023633221450271957225463765963743017724253537983209940374795849573940987640179394910956915229425092884766387602600771061572172,
   51989558076288528109431186203688161693596738436815574463553430433388605806796406700534688559678058422860,
   162322125417717354103539475908042047320809564721494365051797891763361826009188083270137437310623312002389568540490187905121161982299096802342436438018495124942815855265789975830691562356885960471053313317817624834630675352267201433098451627063140940,
   393025636033100, 125353248006072630288555288271693059744332,
   121541389393052762314851990507999404279222748544047723844813480524,
   28298559922969564450796623757721487448006547452107448908,
   35291329353814753176214396833692251357626715144597561932,
   168452009286192075921636420375493040926578088978900599258425588191554488263244,
   161658434011133078258792495374239738066030679284814678091382516095022699143756,
   34237349847258110842626472771157683940195988674664227404,
   573591526811827152808495975196187797448002038284181386543614830741912192853022031503948,
   100178257981531719000666588693879843226560174125465848696178182438571880280488461282614971781325019162945832955840366523451056761172263508075911923864640187831883486485267239108797321208396,
   133159745078015658685716199318416905333866682370480420762166556974869716018947979317524139562626534059813554074026391406725008880335512158458029798834762404351649255744621912873327847733780483153188431961850870669427748921932,
   111347874144006723251740315082759635432460193350070178465876226008240253253465016690222180042393683791803340490905319758907230252916336761275678474809718916962527428299625195504490967045906801319764556,
   430262341800929705094524800640097281340494260320208923077322999007530043461153300120257957953120329791714894123603199281580754447563722731946593052494625609350222264187235867200788558066755987857996,
   1912738769623910984645076069494055500,
   1680712272659881660525487502500380007858136978300551644199099741259326499412807955217462405939232220105290106957352375276471186762109666258078623427599189099712729782684471337612895563655448126028,
   1045909815045116443415854672273274136195051649415069756085133503123906689702611940791514591009503087375931753621166504367266926131176012]

theorem gSymCodes_eq :
    (kernelSyms c).map (fun k => KoreAML.Distinct.strCode (c.symName k.name)) = gSymCodes := by
  decide +kernel

/-- Two names are equal exactly where their codes are (`strCode_inj`). -/
theorem symCode_beq (a b : String) :
    (KoreAML.Distinct.strCode a == KoreAML.Distinct.strCode b) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact ⟨fun h => KoreAML.Distinct.strCode_inj h, fun h => h ▸ rfl⟩

/-! ## Consistency for every H -/

def callOrder : List Nat := []

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

theorem obl_nil (H : HookParams) : FnObligations (cH H) callOrder [] :=
  FnObligations.of_nil
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named)

theorem fnHypH (H : HookParams) : FnHyp (cH H) := fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H
  ParamsTotal.nil (obl_nil H)

/-- **Γ with the step's closure has a model, for every H.** -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

/-! ## Set idempotence (61): refuted -/

section Idem
variable (H : HookParams)

/-- The text's variable `K:SortSet{}`. -/
def kVar : Kore.Pattern := KoreAML.ev "K" (KoreAML.srt "Set")

theorem idem_pattern : U.ax550.ax.pattern = .equals (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]) kVar := by
  decide +kernel
theorem idem_trS : (trS U.ax550).pat = (trAxiom [] [] U.ax550).pat := by decide +kernel

/-- `0` as a KItem, and the set `SetItem(0)`. -/
def a0 : GroundTerm := .inj Srt.int Srt.kitem (.dv Srt.int (.int 0))
def s1 : GroundTerm := .set Srt.set [a0]

theorem s1_sort : (cH H).sortOf s1 = some Srt.set := by rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel
theorem concat_sig : (⟨setConcat, [Srt.set, Srt.set], Srt.set⟩ : CtorSig) ∈ hookSigs := by decide +kernel
theorem concat_args : (cH H).sortsOf [s1, s1] = some [Srt.set, Srt.set] := by
  rw [Semantics.sortsOf_withHooks _ _ noRaw]; decide +kernel
theorem concat_none : hook setConcat [s1, s1] = some none := by decide +kernel
theorem concat_heard : silent setConcat [s1, s1] = false := by decide +kernel
theorem set_numbered : Srt.set < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.set < nRegSorts + c.sortNames.length)
theorem set_name : (cH H).sortName Srt.set = "Set" := (by decide +kernel : c.sortName Srt.set = "Set")
theorem idem_vars : (U.ax550.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax550.ax.pattern).eraseDups =
    [.sortVar "R", .evar "K" (KoreAML.srt "Set")] := by decide +kernel
theorem idem_sort : KoreAML.sortOf [] U.ax550.ax.pattern = some KoreAML.R := by decide +kernel
theorem symApp_withHooks (f : Sym) (ps : List Kore.Pattern) : symApp (cH H) f ps = symApp c f ps := rfl

/-- **Sentence 550 is refuted, for every H**: Γ with it has no model. At `K = SetItem(0)` the
sentence says `_Set_(K, K)` denotes `K`'s element, and `ΓDomains` (the hook's graph, the two sets
sharing a member) says it denotes nothing. -/
theorem idem_refuted : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax550).pat) := by
  intro M _ I hI hax
  rw [idem_trS] at hax
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  obtain ⟨σS, hσS1, hσS2⟩ := sortSing hI (set_numbered H)
  rw [set_name] at hσS1
  obtain ⟨hes, hesort⟩ := elemOf_spec hI (s1_sort H) KoreAML.val0
  rw [set_name] at hesort
  let a := elemOf (cH H) I s1
  have ha : KoreAML.Inh I σS a := (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσS1).mp hesort
  let tbl : KoreAML.VarTable := KoreAML.tableOf U.ax550.ax.sortVars U.ax550.ax.pattern
  let val : KoreAML.VarKey → M := fun
    | .sortVar _ => σS
    | _ => a
  let e' : Valuation M := valOf tbl val
  have hRmem : KoreAML.VarKey.sortVar "R" ∈ tbl := by decide +kernel
  have hKmem : KoreAML.VarKey.evar "K" (KoreAML.srt "Set") ∈ tbl := by decide +kernel
  have hRv : ∀ b, (KoreAML.trSort tbl KoreAML.R).interpret I e' b ↔ b = σS := fun b => by
    rw [trSort_R, KoreAML.interp_evar, valOf_ev hRmem]
  have hKv : e'.evalEvar (tbl.ev (.evar "K" (KoreAML.srt "Set"))) = a := valOf_ev hKmem
  have hg : ∀ k ∈ (U.ax550.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax550.ax.pattern).eraseDups,
      ∀ m, (KoreAML.guardOf tbl k).interpret I e' m := by
    intro k hk m
    rw [idem_vars] at hk
    rcases List.mem_cons.mp hk with rfl | hk
    · rw [KoreAML.interp_guard_sortVar hD, valOf_ev hRmem]
      exact hσS2
    · rw [List.mem_singleton.mp hk, KoreAML.interp_guard_evar hD, trSort_srt, hKv]
      exact hesort
  have hP := (KoreAML.trAxiom_at hD hax e' hg a).mpr (by
    rw [idem_sort]
    show (KoreAML.inhOf (KoreAML.trSort tbl KoreAML.R)).interpret I e' a
    rw [KoreAML.interp_inhOf_of hRv]; exact ha)
  have hP : (KoreAML.tr ⟨tbl, []⟩ (.equals (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]) kVar)).interpret
      I e' a := by
    have := hP; simp only [tbl] at this ⊢; rw [idem_pattern] at this ⊢; exact this
  have hS : ∀ b, (KoreAML.trSort tbl (srtOf c Srt.set)).interpret I e' b ↔ b = σS := fun b => by
    unfold srtOf; rw [show c.sortName Srt.set = "Set" from set_name H, trSort_srt]; exact hσS1 b
  rw [KoreAML.tr, KoreAML.interp_sEquals hD hc hS hRv hσS2 hσS2] at hP
  obtain ⟨-, hall⟩ := hP
  have hK : ∀ b, (KoreAML.tr ⟨tbl, []⟩ kVar).interpret I e' b ↔ b = a := fun b => by
    unfold kVar KoreAML.ev
    rw [KoreAML.tr, KoreAML.interp_evar]
    show b = e'.evalEvar (tbl.ev (.evar "K" (KoreAML.srt "Set"))) ↔ b = a
    rw [hKv]
  have happ := (hall a ha).mpr ((hK a).mpr rfl)
  rw [tr_symApp, KoreAML.trArgs_cons, KoreAML.trArgs_cons, KoreAML.trArgs_nil] at happ
  have hden : (KoreAML.den (symApp (cH H) setConcat (GroundTerm.koreList (cH H) [s1, s1]))).interpret I KoreAML.val0 a := by
    unfold KoreAML.den
    rw [symApp_withHooks, tr_symApp]
    simp only [GroundTerm.koreList]
    rw [KoreAML.trArgs_cons, KoreAML.trArgs_cons, KoreAML.trArgs_nil]
    obtain ⟨f1, b1, hf1, hb1, h1⟩ := KoreAML.interp_app.mp happ
    obtain ⟨f0, b0, hf0, hb0, h0⟩ := KoreAML.interp_app.mp hf1
    refine KoreAML.interp_app.mpr ⟨f1, b1, KoreAML.interp_app.mpr ⟨f0, b0, ?_, (hes b0).mpr ((hK b0).mp hb0), h0⟩,
      (hes b1).mpr ((hK b1).mp hb1), h1⟩
    exact (sym_congr (e := KoreAML.val0) (e' := e') _ f0).mpr hf0
  have hgraph := sat_dom hI (Or.inl ⟨_, [s1, s1], none, concat_sig, concat_args H, concat_none,
    fun _ => concat_heard, rfl⟩)
  exact ((KoreAML.interp_equal hD).mp (hgraph KoreAML.val0 default) a).mp hden

end Idem


end KCore.TieRdrConfigDeep

#check @KCore.TieRdrConfigDeep.noRaw
#check @KCore.TieRdrConfigDeep.readsConfined_c
#check @KCore.TieRdrConfigDeep.userAxioms_eq
#check @KCore.TieRdrConfigDeep.coreOK
#check @KCore.TieRdrConfigDeep.wf_defn
#check @KCore.TieRdrConfigDeep.account
#check @KCore.TieRdrConfigDeep.account_sizes
#check @KCore.TieRdrConfigDeep.account_classes
#check @KCore.TieRdrConfigDeep.lists_in_account
#check @KCore.TieRdrConfigDeep.consistent
#check @KCore.TieRdrConfigDeep.idem_refuted
#print axioms KCore.TieRdrConfigDeep.noRaw
#print axioms KCore.TieRdrConfigDeep.readsConfined_c
#print axioms KCore.TieRdrConfigDeep.userAxioms_eq
#print axioms KCore.TieRdrConfigDeep.coreOK
#print axioms KCore.TieRdrConfigDeep.wf_defn
#print axioms KCore.TieRdrConfigDeep.account
#print axioms KCore.TieRdrConfigDeep.account_sizes
#print axioms KCore.TieRdrConfigDeep.account_classes
#print axioms KCore.TieRdrConfigDeep.lists_in_account
#print axioms KCore.TieRdrConfigDeep.consistent
#print axioms KCore.TieRdrConfigDeep.idem_refuted
