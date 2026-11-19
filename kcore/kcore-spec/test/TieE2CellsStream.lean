/-
  The tie (C14) on `f2-examples/e2-cells-stream.kompile.kore`, the kompiled text of construct fixture e2-cells-stream
  (`test/constructs/fixtures/e2-cells-stream`), sentence by sentence, against the translation of the text as
  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for
  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by
  `test/constructs/tiegen.py e2-cells-stream`; run from the package root: `lake env lean -j1 test/TieE2CellsStream.lean`.

  Layer 1.
  - `wf_defn`: `wf defn = true`.
  - The account: the class lists partition the 2997 sentences of the user module E2-CELLS-STREAM, in
    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds
    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).
  - `absent_proj_below`: the 27 no-direction sentences that are equations of a projection
    `project:X` are of sorts X that are K, KItem or below KItem in Γ (`GenEqs.projBelowB`).
  - `attrs_agree`: the attributes the translation does not read agree with `defn`.
  - `sig_origin`: each of the 323 items of `sigItems c` is a declaration's item of the text or a
    surplus one; `decls_entailed`: Γ entails the item of each declaration without sort parameters
    of a symbol Γ has (both by ranges of the lists).
  - The definition reads no confined sort (`readsConfined_c`), has no open generator (`noRaw`) and
    owes no fact (`term_named`, `total_named`, `agree_named`, `match_named`), so Γ with the step's
    closure has a model for every H (`consistent`).

  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).
  - Function equations (58, and two sentences of the text's prelude modules, 1 (KSEQ), 2 (KSEQ),
    which no user sentence is): each of Γ's items is the translation of one sentence, in the order
    `fnText` lists them (`fn_shape`); its user-module sentences are the class, the others those
    prelude sentences (`fns_account`, and `preludeKseq_eq`: they are the text's); `fns_entailed`
    (E), `fns_from_text` (the converse), `fn_prios` (the priorities the sentences state are the
    clauses').
  - Rewrite rules (8): each of Γ's rule items (with the premise `⌈rhs ∧ ens⌉`) is a consequence
    of its text sentence, `ruleText` in `ruleItems`' order (`rule_from_text`, W1, every H).
    Rules 0, 1, 2, 3, 4 have rules of a smaller priority: Γ's item has also the premise
    `¬ ⋁ competitors`, that none of them applies, which the sentence states by its priority
    attribute only (`rule_prios`); the item without both premises is the sentence (`rule<j>_text`,
    `item_of_minusComp`).
  - Constructor sentences (2635): entailed by Γ (`cons_entailed`).
  - No junk (5 of a sort without generators, `nojunk_trivial_entailed`; 15 equal to
    one of Γ's constructor items, `nojunk_items`; 1 KItem's with its disjuncts in the text's
    order, `nojunk_kitem_entailed`).
  - Set idempotence (2685): Γ with it has no model (`idem_refuted`).
  - Library sample, 2837 (`I -Int 0 = I`): holds at values (`lib166`, `lib166_at_values`).
  - The converse over Γ's content: each premise is a function sentence's translation, one of the
    five parts Γ defines by predicates, or definedness (`gamma_origin`, `gamma_from`).
  - Hooked functional, collection law, library: at values (no theorem here); function functional:
    owed as `FnHyp` (no theorem); parameter functional: owed as `ParamsTotal`
    (`total_params`, `paramfunctional_account`, `paramfunctional_heads`); no direction: `absent_closed`.

  IOError's no junk (2764) is entailed (`nojunk_ioerror_entailed`): its item lists IOError's
  generators in another order than `Semantics.gens`. IOInt's no junk (2766) is entailed
  (`nojunk_ioint_entailed`): its item lists IOInt's generators in the text's order. IOString's no
  junk (2767) is entailed (`nojunk_iostring_entailed`): its item lists IOString's generators in the
  text's order. Stream's no junk (2777) is entailed (`nojunk_stream_entailed`): its item lists
  Stream's generators in another order than `Semantics.gens`.

  The parameter functional sentence (2645) is the `functional` sentence of a parameter symbol no
  registry hook interprets that the text declares total (`Definition.totalParams`, `total_params`),
  which the reader reads as that declaration. Γ states the parameter's graph at values from the
  interpretation (`ΓDomains`: its application to values denotes `paramVal`'s value, or nothing), so
  the sentence holds at values where H gives the parameter a value of its sort at every argument
  list of its sorts: the hypothesis on H the statements take (`ParamsTotal`). The account holds it
  in the class `parameter functional`, of the direction `hypothesis` (`paramfunctional_account`),
  and every such sentence of the user module is in it (`paramfunctional_heads`).

  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` (2758);
  the sentences of a class with a theorem that no theorem here holds of are `uncovered` (0).
  Written with `--split`: this file holds the literals, the names, `wf`, the account, the
  consistency and the sections that read none of the other files' decisions; the other sections are
  in `test/TieE2CellsStreamAttrs.lean`, `test/TieE2CellsStreamSig.lean`,
  `test/TieE2CellsStreamDecls.lean`, `test/TieE2CellsStreamFns.lean`,
  `test/TieE2CellsStreamNoJunk.lean`, `test/TieE2CellsStreamCons.lean`,
  `test/TieE2CellsStreamAbsent.lean`, `test/TieE2CellsStreamDeclCounts.lean`, in this namespace,
  each of which repeats the literals and the definitions and facts it reads, as a test file imports
  no test file.

  Measured alone (LEAN_NUM_THREADS=1, `lake env lean -j1`, a 12G memory scope): 122 s, peak
  9.0 GiB.
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

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The definition reads no confined sort: its theory is Γ. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E2-CELLS-STREAM")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl
theorem userAxioms_length : U.all.length = 2997 := by decide +kernel

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl

/-! ## Layer 1 -/

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

set_option maxHeartbeats 1000000 in
theorem wf_defn : wf defn = true := by decide_cheap

/-! ## The account: every sentence of the user module is in exactly one class -/

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

/-- The indices of the user module's sentences, in text order, are 4, …, 3000. -/
theorem indices_eq : U.all.map (·.index) = List.range' 4 2997 := by decide +kernel

/-- The class lists, sorted (13 passes of `KoreAML.Distinct.msort`), are the same range. -/
theorem classes_sorted : KoreAML.Distinct.msort 13 (classes.flatMap (·.2)) = List.range' 4 2997 := by
  decide +kernel

/-- **The account**: the class lists partition the user module's sentences. Their concatenation is
a permutation of the sentences' indices, which are distinct, so each sentence is in one class and
in it once: sorted, the class lists are the range the indices are (`tacAccount_of_msort`). -/
theorem account : (classes.flatMap (·.2)).isPerm (userAxioms.map (·.index)) = true ∧
    (userAxioms.map (·.index)).Nodup :=
  tacAccount_of_msort classes_sorted (by rw [userAxioms_eq]; exact indices_eq)

/-- The class sizes. -/
theorem account_sizes : classes.map (fun cl => (cl.1, cl.2.length)) =
    [("function equation", 58), ("rewrite rule", 8), ("priority equation", 0), ("constructor functional", 91), ("subsort", 37), ("injectivity", 16), ("distinctness", 2491), ("no junk", 25), ("function functional", 29), ("hooked functional", 61), ("collection law", 9), ("library", 101), ("set idempotence", 1), ("set-variable lemma", 6), ("function law", 0), ("open generator law", 0), ("open generator functional", 0), ("parameter functional", 1), ("parameter lemma", 0), ("user lemma", 0), ("user lemma at values", 0), ("no direction", 63)] := by
  decide +kernel

/-- The classes are the tie's (`tieClasses`, which gives each its direction), in its order. -/
theorem account_classes : classes.map (·.1) = tieClasses.map (·.1) := by decide +kernel

/-- The sentences whose text is none of f2-examples/ens.kompile.kore's user module, with their class. -/
def unmapped : List (Nat × String) :=
  [(4, "subsort"), (5, "subsort"), (8, "subsort"), (9, "subsort"), (13, "subsort"),
   (14, "subsort"), (17, "subsort"), (20, "subsort"), (22, "subsort"), (23, "subsort"),
   (24, "subsort"), (25, "subsort"), (26, "subsort"), (28, "subsort"), (29, "subsort"),
   (30, "subsort"), (32, "subsort"), (34, "subsort"), (35, "subsort"), (36, "subsort"),
   (37, "subsort"), (38, "subsort"), (39, "subsort"), (41, "constructor functional"),
   (42, "distinctness"), (43, "distinctness"), (44, "distinctness"), (45, "distinctness"),
   (46, "distinctness"), (47, "distinctness"), (48, "distinctness"), (49, "distinctness"),
   (50, "distinctness"), (51, "distinctness"), (52, "distinctness"), (53, "distinctness"),
   (54, "distinctness"), (55, "distinctness"), (56, "distinctness"), (57, "distinctness"),
   (58, "distinctness"), (59, "distinctness"), (60, "distinctness"), (61, "distinctness"),
   (62, "distinctness"), (63, "distinctness"), (64, "distinctness"), (65, "distinctness"),
   (66, "distinctness"), (67, "distinctness"), (68, "distinctness"), (69, "distinctness"),
   (70, "distinctness"), (71, "distinctness"), (72, "distinctness"), (73, "distinctness"),
   (74, "distinctness"), (75, "distinctness"), (76, "distinctness"), (77, "distinctness"),
   (78, "distinctness"), (79, "distinctness"), (80, "distinctness"), (81, "distinctness"),
   (82, "distinctness"), (83, "distinctness"), (84, "distinctness"), (85, "distinctness"),
   (86, "distinctness"), (87, "distinctness"), (88, "distinctness"), (89, "distinctness"),
   (90, "distinctness"), (91, "distinctness"), (92, "distinctness"), (93, "distinctness"),
   (94, "distinctness"), (95, "distinctness"), (96, "distinctness"), (97, "distinctness"),
   (98, "distinctness"), (99, "distinctness"), (100, "distinctness"), (101, "distinctness"),
   (102, "distinctness"), (103, "distinctness"), (104, "distinctness"), (105, "distinctness"),
   (106, "distinctness"), (107, "distinctness"), (108, "distinctness"), (109, "distinctness"),
   (110, "distinctness"), (111, "distinctness"), (112, "constructor functional"),
   (113, "distinctness"), (114, "distinctness"), (115, "distinctness"), (116, "distinctness"),
   (117, "distinctness"), (118, "distinctness"), (119, "distinctness"), (120, "distinctness"),
   (121, "distinctness"), (122, "distinctness"), (123, "distinctness"), (124, "distinctness"),
   (125, "distinctness"), (126, "distinctness"), (127, "distinctness"), (128, "distinctness"),
   (129, "distinctness"), (130, "distinctness"), (131, "distinctness"), (132, "distinctness"),
   (133, "distinctness"), (134, "distinctness"), (135, "distinctness"), (136, "distinctness"),
   (137, "distinctness"), (138, "distinctness"), (139, "distinctness"), (140, "distinctness"),
   (141, "distinctness"), (142, "distinctness"), (143, "distinctness"), (144, "distinctness"),
   (145, "distinctness"), (146, "distinctness"), (147, "distinctness"), (148, "distinctness"),
   (149, "distinctness"), (150, "distinctness"), (151, "distinctness"), (152, "distinctness"),
   (153, "distinctness"), (154, "distinctness"), (155, "distinctness"), (156, "distinctness"),
   (157, "distinctness"), (158, "distinctness"), (159, "distinctness"), (160, "distinctness"),
   (161, "distinctness"), (162, "distinctness"), (163, "distinctness"), (164, "distinctness"),
   (165, "distinctness"), (166, "distinctness"), (167, "distinctness"), (168, "distinctness"),
   (169, "distinctness"), (170, "distinctness"), (171, "distinctness"), (172, "distinctness"),
   (173, "distinctness"), (174, "distinctness"), (175, "distinctness"), (176, "distinctness"),
   (177, "distinctness"), (178, "distinctness"), (179, "distinctness"), (180, "distinctness"),
   (181, "distinctness"), (182, "constructor functional"), (183, "distinctness"),
   (184, "distinctness"), (185, "distinctness"), (186, "distinctness"), (187, "distinctness"),
   (188, "distinctness"), (189, "distinctness"), (190, "distinctness"), (191, "distinctness"),
   (192, "distinctness"), (193, "distinctness"), (194, "distinctness"), (195, "distinctness"),
   (196, "distinctness"), (197, "distinctness"), (198, "distinctness"), (199, "distinctness"),
   (200, "distinctness"), (201, "distinctness"), (202, "distinctness"), (203, "distinctness"),
   (204, "distinctness"), (205, "distinctness"), (206, "distinctness"), (207, "distinctness"),
   (208, "distinctness"), (209, "distinctness"), (210, "distinctness"), (211, "distinctness"),
   (212, "distinctness"), (213, "distinctness"), (214, "distinctness"), (215, "distinctness"),
   (216, "distinctness"), (217, "distinctness"), (218, "distinctness"), (219, "distinctness"),
   (220, "distinctness"), (221, "distinctness"), (222, "distinctness"), (223, "distinctness"),
   (224, "distinctness"), (225, "distinctness"), (226, "distinctness"), (227, "distinctness"),
   (228, "distinctness"), (229, "distinctness"), (230, "distinctness"), (231, "distinctness"),
   (232, "distinctness"), (233, "distinctness"), (234, "distinctness"), (235, "distinctness"),
   (236, "distinctness"), (237, "distinctness"), (238, "distinctness"), (239, "distinctness"),
   (240, "distinctness"), (241, "distinctness"), (242, "distinctness"), (243, "distinctness"),
   (244, "distinctness"), (245, "distinctness"), (246, "distinctness"), (247, "distinctness"),
   (248, "distinctness"), (249, "distinctness"), (250, "distinctness"),
   (251, "constructor functional"), (252, "distinctness"), (253, "distinctness"),
   (254, "distinctness"), (255, "distinctness"), (256, "distinctness"), (257, "distinctness"),
   (258, "distinctness"), (259, "distinctness"), (260, "distinctness"), (261, "distinctness"),
   (262, "distinctness"), (263, "distinctness"), (264, "distinctness"), (265, "distinctness"),
   (266, "distinctness"), (267, "distinctness"), (268, "distinctness"), (269, "distinctness"),
   (270, "distinctness"), (271, "distinctness"), (272, "distinctness"), (273, "distinctness"),
   (274, "distinctness"), (275, "distinctness"), (276, "distinctness"), (277, "distinctness"),
   (278, "distinctness"), (279, "distinctness"), (280, "distinctness"), (281, "distinctness"),
   (282, "distinctness"), (283, "distinctness"), (284, "distinctness"), (285, "distinctness"),
   (286, "distinctness"), (287, "distinctness"), (288, "distinctness"), (289, "distinctness"),
   (290, "distinctness"), (291, "distinctness"), (292, "distinctness"), (293, "distinctness"),
   (294, "distinctness"), (295, "distinctness"), (296, "distinctness"), (297, "distinctness"),
   (298, "distinctness"), (299, "distinctness"), (300, "distinctness"), (301, "distinctness"),
   (302, "distinctness"), (303, "distinctness"), (304, "distinctness"), (305, "distinctness"),
   (306, "distinctness"), (307, "distinctness"), (308, "distinctness"), (309, "distinctness"),
   (310, "distinctness"), (311, "distinctness"), (312, "distinctness"), (313, "distinctness"),
   (314, "distinctness"), (315, "distinctness"), (316, "distinctness"), (317, "distinctness"),
   (318, "distinctness"), (319, "constructor functional"), (320, "distinctness"),
   (321, "distinctness"), (322, "distinctness"), (323, "distinctness"), (324, "distinctness"),
   (325, "distinctness"), (326, "distinctness"), (327, "distinctness"), (328, "distinctness"),
   (329, "distinctness"), (330, "distinctness"), (331, "distinctness"), (332, "distinctness"),
   (333, "distinctness"), (334, "distinctness"), (335, "distinctness"), (336, "distinctness"),
   (337, "distinctness"), (338, "distinctness"), (339, "distinctness"), (340, "distinctness"),
   (341, "distinctness"), (342, "distinctness"), (343, "distinctness"), (344, "distinctness"),
   (345, "distinctness"), (346, "distinctness"), (347, "distinctness"), (348, "distinctness"),
   (349, "distinctness"), (350, "distinctness"), (351, "distinctness"), (352, "distinctness"),
   (353, "distinctness"), (354, "distinctness"), (355, "distinctness"), (356, "distinctness"),
   (357, "distinctness"), (358, "distinctness"), (359, "distinctness"), (360, "distinctness"),
   (361, "distinctness"), (362, "distinctness"), (363, "distinctness"), (364, "distinctness"),
   (365, "distinctness"), (366, "distinctness"), (367, "distinctness"), (368, "distinctness"),
   (369, "distinctness"), (370, "distinctness"), (371, "distinctness"), (372, "distinctness"),
   (373, "distinctness"), (374, "distinctness"), (375, "distinctness"), (376, "distinctness"),
   (377, "distinctness"), (378, "distinctness"), (379, "distinctness"), (380, "distinctness"),
   (381, "distinctness"), (382, "distinctness"), (383, "distinctness"), (384, "distinctness"),
   (385, "distinctness"), (386, "constructor functional"), (387, "distinctness"),
   (388, "distinctness"), (389, "distinctness"), (390, "distinctness"), (391, "distinctness"),
   (392, "distinctness"), (393, "distinctness"), (394, "distinctness"), (395, "distinctness"),
   (396, "distinctness"), (397, "distinctness"), (398, "distinctness"), (399, "distinctness"),
   (400, "distinctness"), (401, "distinctness"), (402, "distinctness"), (403, "distinctness"),
   (404, "distinctness"), (405, "distinctness"), (406, "distinctness"), (407, "distinctness"),
   (408, "distinctness"), (409, "distinctness"), (410, "distinctness"), (411, "distinctness"),
   (412, "distinctness"), (413, "distinctness"), (414, "distinctness"), (415, "distinctness"),
   (416, "distinctness"), (417, "distinctness"), (418, "distinctness"), (419, "distinctness"),
   (420, "distinctness"), (421, "distinctness"), (422, "distinctness"), (423, "distinctness"),
   (424, "distinctness"), (425, "distinctness"), (426, "distinctness"), (427, "distinctness"),
   (428, "distinctness"), (429, "distinctness"), (430, "distinctness"), (431, "distinctness"),
   (432, "distinctness"), (433, "distinctness"), (434, "distinctness"), (435, "distinctness"),
   (436, "distinctness"), (437, "distinctness"), (438, "distinctness"), (439, "distinctness"),
   (440, "distinctness"), (441, "distinctness"), (442, "distinctness"), (443, "distinctness"),
   (444, "distinctness"), (445, "distinctness"), (446, "distinctness"), (447, "distinctness"),
   (448, "distinctness"), (449, "distinctness"), (450, "distinctness"), (451, "distinctness"),
   (452, "constructor functional"), (453, "distinctness"), (454, "distinctness"),
   (455, "distinctness"), (456, "distinctness"), (457, "distinctness"), (458, "distinctness"),
   (459, "distinctness"), (460, "distinctness"), (461, "distinctness"), (462, "distinctness"),
   (463, "distinctness"), (464, "distinctness"), (465, "distinctness"), (466, "distinctness"),
   (467, "distinctness"), (468, "distinctness"), (469, "distinctness"), (470, "distinctness"),
   (471, "distinctness"), (472, "distinctness"), (473, "distinctness"), (474, "distinctness"),
   (475, "distinctness"), (476, "distinctness"), (477, "distinctness"), (478, "distinctness"),
   (479, "distinctness"), (480, "distinctness"), (481, "distinctness"), (482, "distinctness"),
   (483, "distinctness"), (484, "distinctness"), (485, "distinctness"), (486, "distinctness"),
   (487, "distinctness"), (488, "distinctness"), (489, "distinctness"), (490, "distinctness"),
   (491, "distinctness"), (492, "distinctness"), (493, "distinctness"), (494, "distinctness"),
   (495, "distinctness"), (496, "distinctness"), (497, "distinctness"), (498, "distinctness"),
   (499, "distinctness"), (500, "distinctness"), (501, "distinctness"), (502, "distinctness"),
   (503, "distinctness"), (504, "distinctness"), (505, "distinctness"), (506, "distinctness"),
   (507, "distinctness"), (508, "distinctness"), (509, "distinctness"), (510, "distinctness"),
   (511, "distinctness"), (512, "distinctness"), (513, "distinctness"), (514, "distinctness"),
   (515, "distinctness"), (516, "distinctness"), (517, "constructor functional"),
   (518, "distinctness"), (519, "distinctness"), (520, "distinctness"), (521, "distinctness"),
   (522, "distinctness"), (523, "distinctness"), (524, "distinctness"), (525, "distinctness"),
   (526, "distinctness"), (527, "distinctness"), (528, "distinctness"), (529, "distinctness"),
   (530, "distinctness"), (531, "distinctness"), (532, "distinctness"), (533, "distinctness"),
   (534, "distinctness"), (535, "distinctness"), (536, "distinctness"), (537, "distinctness"),
   (538, "distinctness"), (539, "distinctness"), (540, "distinctness"), (541, "distinctness"),
   (542, "distinctness"), (543, "distinctness"), (544, "distinctness"), (545, "distinctness"),
   (546, "distinctness"), (547, "distinctness"), (548, "distinctness"), (549, "distinctness"),
   (550, "distinctness"), (551, "distinctness"), (552, "distinctness"), (553, "distinctness"),
   (554, "distinctness"), (555, "distinctness"), (556, "distinctness"), (557, "distinctness"),
   (558, "distinctness"), (559, "distinctness"), (560, "distinctness"), (561, "distinctness"),
   (562, "distinctness"), (563, "distinctness"), (564, "distinctness"), (565, "distinctness"),
   (566, "distinctness"), (567, "distinctness"), (568, "distinctness"), (569, "distinctness"),
   (570, "distinctness"), (571, "distinctness"), (572, "distinctness"), (573, "distinctness"),
   (574, "distinctness"), (575, "distinctness"), (576, "distinctness"), (577, "distinctness"),
   (578, "distinctness"), (579, "distinctness"), (580, "distinctness"),
   (581, "constructor functional"), (582, "distinctness"), (583, "distinctness"),
   (584, "distinctness"), (585, "distinctness"), (586, "distinctness"), (587, "distinctness"),
   (588, "distinctness"), (589, "distinctness"), (590, "distinctness"), (591, "distinctness"),
   (592, "distinctness"), (593, "distinctness"), (594, "distinctness"), (595, "distinctness"),
   (596, "distinctness"), (597, "distinctness"), (598, "distinctness"), (599, "distinctness"),
   (600, "distinctness"), (601, "distinctness"), (602, "distinctness"), (603, "distinctness"),
   (604, "distinctness"), (605, "distinctness"), (606, "distinctness"), (607, "distinctness"),
   (608, "distinctness"), (609, "distinctness"), (610, "distinctness"), (611, "distinctness"),
   (612, "distinctness"), (613, "distinctness"), (614, "distinctness"), (615, "distinctness"),
   (616, "distinctness"), (617, "distinctness"), (618, "distinctness"), (619, "distinctness"),
   (620, "distinctness"), (621, "distinctness"), (622, "distinctness"), (623, "distinctness"),
   (624, "distinctness"), (625, "distinctness"), (626, "distinctness"), (627, "distinctness"),
   (628, "distinctness"), (629, "distinctness"), (630, "distinctness"), (631, "distinctness"),
   (632, "distinctness"), (633, "distinctness"), (634, "distinctness"), (635, "distinctness"),
   (636, "distinctness"), (637, "distinctness"), (638, "distinctness"), (639, "distinctness"),
   (640, "distinctness"), (641, "distinctness"), (642, "distinctness"), (643, "distinctness"),
   (644, "constructor functional"), (645, "distinctness"), (646, "distinctness"),
   (647, "distinctness"), (648, "distinctness"), (649, "distinctness"), (650, "distinctness"),
   (651, "distinctness"), (652, "distinctness"), (653, "distinctness"), (654, "distinctness"),
   (655, "distinctness"), (656, "distinctness"), (657, "distinctness"), (658, "distinctness"),
   (659, "distinctness"), (660, "distinctness"), (661, "distinctness"), (662, "distinctness"),
   (663, "distinctness"), (664, "distinctness"), (665, "distinctness"), (666, "distinctness"),
   (667, "distinctness"), (668, "distinctness"), (669, "distinctness"), (670, "distinctness"),
   (671, "distinctness"), (672, "distinctness"), (673, "distinctness"), (674, "distinctness"),
   (675, "distinctness"), (676, "distinctness"), (677, "distinctness"), (678, "distinctness"),
   (679, "distinctness"), (680, "distinctness"), (681, "distinctness"), (682, "distinctness"),
   (683, "distinctness"), (684, "distinctness"), (685, "distinctness"), (686, "distinctness"),
   (687, "distinctness"), (688, "distinctness"), (689, "distinctness"), (690, "distinctness"),
   (691, "distinctness"), (692, "distinctness"), (693, "distinctness"), (694, "distinctness"),
   (695, "distinctness"), (696, "distinctness"), (697, "distinctness"), (698, "distinctness"),
   (699, "distinctness"), (700, "distinctness"), (701, "distinctness"), (702, "distinctness"),
   (703, "distinctness"), (704, "distinctness"), (705, "distinctness"),
   (706, "constructor functional"), (707, "distinctness"), (708, "distinctness"),
   (709, "distinctness"), (710, "distinctness"), (711, "distinctness"), (712, "distinctness"),
   (713, "distinctness"), (714, "distinctness"), (715, "distinctness"), (716, "distinctness"),
   (717, "distinctness"), (718, "distinctness"), (719, "distinctness"), (720, "distinctness"),
   (721, "distinctness"), (722, "distinctness"), (723, "distinctness"), (724, "distinctness"),
   (725, "distinctness"), (726, "distinctness"), (727, "distinctness"), (728, "distinctness"),
   (729, "distinctness"), (730, "distinctness"), (731, "distinctness"), (732, "distinctness"),
   (733, "distinctness"), (734, "distinctness"), (735, "distinctness"), (736, "distinctness"),
   (737, "distinctness"), (738, "distinctness"), (739, "distinctness"), (740, "distinctness"),
   (741, "distinctness"), (742, "distinctness"), (743, "distinctness"), (744, "distinctness"),
   (745, "distinctness"), (746, "distinctness"), (747, "distinctness"), (748, "distinctness"),
   (749, "distinctness"), (750, "distinctness"), (751, "distinctness"), (752, "distinctness"),
   (753, "distinctness"), (754, "distinctness"), (755, "distinctness"), (756, "distinctness"),
   (757, "distinctness"), (758, "distinctness"), (759, "distinctness"), (760, "distinctness"),
   (761, "distinctness"), (762, "distinctness"), (763, "distinctness"), (764, "distinctness"),
   (765, "distinctness"), (766, "distinctness"), (767, "constructor functional"),
   (768, "distinctness"), (769, "distinctness"), (770, "distinctness"), (771, "distinctness"),
   (772, "distinctness"), (773, "distinctness"), (774, "distinctness"), (775, "distinctness"),
   (776, "distinctness"), (777, "distinctness"), (778, "distinctness"), (779, "distinctness"),
   (780, "distinctness"), (781, "distinctness"), (782, "distinctness"), (783, "distinctness"),
   (784, "distinctness"), (785, "distinctness"), (786, "distinctness"), (787, "distinctness"),
   (788, "distinctness"), (789, "distinctness"), (790, "distinctness"), (791, "distinctness"),
   (792, "distinctness"), (793, "distinctness"), (794, "distinctness"), (795, "distinctness"),
   (796, "distinctness"), (797, "distinctness"), (798, "distinctness"), (799, "distinctness"),
   (800, "distinctness"), (801, "distinctness"), (802, "distinctness"), (803, "distinctness"),
   (804, "distinctness"), (805, "distinctness"), (806, "distinctness"), (807, "distinctness"),
   (808, "distinctness"), (809, "distinctness"), (810, "distinctness"), (811, "distinctness"),
   (812, "distinctness"), (813, "distinctness"), (814, "distinctness"), (815, "distinctness"),
   (816, "distinctness"), (817, "distinctness"), (818, "distinctness"), (819, "distinctness"),
   (820, "distinctness"), (821, "distinctness"), (822, "distinctness"), (823, "distinctness"),
   (824, "distinctness"), (825, "distinctness"), (826, "distinctness"),
   (827, "constructor functional"), (828, "distinctness"), (829, "distinctness"),
   (830, "distinctness"), (831, "distinctness"), (832, "distinctness"), (833, "distinctness"),
   (834, "distinctness"), (835, "distinctness"), (836, "distinctness"), (837, "distinctness"),
   (838, "distinctness"), (839, "distinctness"), (840, "distinctness"), (841, "distinctness"),
   (842, "distinctness"), (843, "distinctness"), (844, "distinctness"), (845, "distinctness"),
   (846, "distinctness"), (847, "distinctness"), (848, "distinctness"), (849, "distinctness"),
   (850, "distinctness"), (851, "distinctness"), (852, "distinctness"), (853, "distinctness"),
   (854, "distinctness"), (855, "distinctness"), (856, "distinctness"), (857, "distinctness"),
   (858, "distinctness"), (859, "distinctness"), (860, "distinctness"), (861, "distinctness"),
   (862, "distinctness"), (863, "distinctness"), (864, "distinctness"), (865, "distinctness"),
   (866, "distinctness"), (867, "distinctness"), (868, "distinctness"), (869, "distinctness"),
   (870, "distinctness"), (871, "distinctness"), (872, "distinctness"), (873, "distinctness"),
   (874, "distinctness"), (875, "distinctness"), (876, "distinctness"), (877, "distinctness"),
   (878, "distinctness"), (879, "distinctness"), (880, "distinctness"), (881, "distinctness"),
   (882, "distinctness"), (883, "distinctness"), (884, "distinctness"), (885, "distinctness"),
   (886, "constructor functional"), (887, "distinctness"), (888, "distinctness"),
   (889, "distinctness"), (890, "distinctness"), (891, "distinctness"), (892, "distinctness"),
   (893, "distinctness"), (894, "distinctness"), (895, "distinctness"), (896, "distinctness"),
   (897, "distinctness"), (898, "distinctness"), (899, "distinctness"), (900, "distinctness"),
   (901, "distinctness"), (902, "distinctness"), (903, "distinctness"), (904, "distinctness"),
   (905, "distinctness"), (906, "distinctness"), (907, "distinctness"), (908, "distinctness"),
   (909, "distinctness"), (910, "distinctness"), (911, "distinctness"), (912, "distinctness"),
   (913, "distinctness"), (914, "distinctness"), (915, "distinctness"), (916, "distinctness"),
   (917, "distinctness"), (918, "distinctness"), (919, "distinctness"), (920, "distinctness"),
   (921, "distinctness"), (922, "distinctness"), (923, "distinctness"), (924, "distinctness"),
   (925, "distinctness"), (926, "distinctness"), (927, "distinctness"), (928, "distinctness"),
   (929, "distinctness"), (930, "distinctness"), (931, "distinctness"), (932, "distinctness"),
   (933, "distinctness"), (934, "distinctness"), (935, "distinctness"), (936, "distinctness"),
   (937, "distinctness"), (938, "distinctness"), (939, "distinctness"), (940, "distinctness"),
   (941, "distinctness"), (942, "distinctness"), (943, "distinctness"),
   (944, "constructor functional"), (945, "distinctness"), (946, "distinctness"),
   (947, "distinctness"), (948, "distinctness"), (949, "distinctness"), (950, "distinctness"),
   (951, "distinctness"), (952, "distinctness"), (953, "distinctness"), (954, "distinctness"),
   (955, "distinctness"), (956, "distinctness"), (957, "distinctness"), (958, "distinctness"),
   (959, "distinctness"), (960, "distinctness"), (961, "distinctness"), (962, "distinctness"),
   (963, "distinctness"), (964, "distinctness"), (965, "distinctness"), (966, "distinctness"),
   (967, "distinctness"), (968, "distinctness"), (969, "distinctness"), (970, "distinctness"),
   (971, "distinctness"), (972, "distinctness"), (973, "distinctness"), (974, "distinctness"),
   (975, "distinctness"), (976, "distinctness"), (977, "distinctness"), (978, "distinctness"),
   (979, "distinctness"), (980, "distinctness"), (981, "distinctness"), (982, "distinctness"),
   (983, "distinctness"), (984, "distinctness"), (985, "distinctness"), (986, "distinctness"),
   (987, "distinctness"), (988, "distinctness"), (989, "distinctness"), (990, "distinctness"),
   (991, "distinctness"), (992, "distinctness"), (993, "distinctness"), (994, "distinctness"),
   (995, "distinctness"), (996, "distinctness"), (997, "distinctness"), (998, "distinctness"),
   (999, "distinctness"), (1000, "distinctness"), (1001, "constructor functional"),
   (1002, "distinctness"), (1003, "distinctness"), (1004, "distinctness"), (1005, "distinctness"),
   (1006, "distinctness"), (1007, "distinctness"), (1008, "distinctness"), (1009, "distinctness"),
   (1010, "distinctness"), (1011, "distinctness"), (1012, "distinctness"), (1013, "distinctness"),
   (1014, "distinctness"), (1015, "distinctness"), (1016, "distinctness"), (1017, "distinctness"),
   (1018, "distinctness"), (1019, "distinctness"), (1020, "distinctness"), (1021, "distinctness"),
   (1022, "distinctness"), (1023, "distinctness"), (1024, "distinctness"), (1025, "distinctness"),
   (1026, "distinctness"), (1027, "distinctness"), (1028, "distinctness"), (1029, "distinctness"),
   (1030, "distinctness"), (1031, "distinctness"), (1032, "distinctness"), (1033, "distinctness"),
   (1034, "distinctness"), (1035, "distinctness"), (1036, "distinctness"), (1037, "distinctness"),
   (1038, "distinctness"), (1039, "distinctness"), (1040, "distinctness"), (1041, "distinctness"),
   (1042, "distinctness"), (1043, "distinctness"), (1044, "distinctness"), (1045, "distinctness"),
   (1046, "distinctness"), (1047, "distinctness"), (1048, "distinctness"), (1049, "distinctness"),
   (1050, "distinctness"), (1051, "distinctness"), (1052, "distinctness"), (1053, "distinctness"),
   (1054, "distinctness"), (1055, "distinctness"), (1056, "distinctness"),
   (1057, "constructor functional"), (1058, "distinctness"), (1059, "distinctness"),
   (1060, "distinctness"), (1061, "distinctness"), (1062, "distinctness"), (1063, "distinctness"),
   (1064, "distinctness"), (1065, "distinctness"), (1066, "distinctness"), (1067, "distinctness"),
   (1068, "distinctness"), (1069, "distinctness"), (1070, "distinctness"), (1071, "distinctness"),
   (1072, "distinctness"), (1073, "distinctness"), (1074, "distinctness"), (1075, "distinctness"),
   (1076, "distinctness"), (1077, "distinctness"), (1078, "distinctness"), (1079, "distinctness"),
   (1080, "distinctness"), (1081, "distinctness"), (1082, "distinctness"), (1083, "distinctness"),
   (1084, "distinctness"), (1085, "distinctness"), (1086, "distinctness"), (1087, "distinctness"),
   (1088, "distinctness"), (1089, "distinctness"), (1090, "distinctness"), (1091, "distinctness"),
   (1092, "distinctness"), (1093, "distinctness"), (1094, "distinctness"), (1095, "distinctness"),
   (1096, "distinctness"), (1097, "distinctness"), (1098, "distinctness"), (1099, "distinctness"),
   (1100, "distinctness"), (1101, "distinctness"), (1102, "distinctness"), (1103, "distinctness"),
   (1104, "distinctness"), (1105, "distinctness"), (1106, "distinctness"), (1107, "distinctness"),
   (1108, "distinctness"), (1109, "distinctness"), (1110, "distinctness"), (1111, "distinctness"),
   (1112, "constructor functional"), (1113, "distinctness"), (1114, "distinctness"),
   (1115, "distinctness"), (1116, "distinctness"), (1117, "distinctness"), (1118, "distinctness"),
   (1119, "distinctness"), (1120, "distinctness"), (1121, "distinctness"), (1122, "distinctness"),
   (1123, "distinctness"), (1124, "distinctness"), (1125, "distinctness"), (1126, "distinctness"),
   (1127, "distinctness"), (1128, "distinctness"), (1129, "distinctness"), (1130, "distinctness"),
   (1131, "distinctness"), (1132, "distinctness"), (1133, "distinctness"), (1134, "distinctness"),
   (1135, "distinctness"), (1136, "distinctness"), (1137, "distinctness"), (1138, "distinctness"),
   (1139, "distinctness"), (1140, "distinctness"), (1141, "distinctness"), (1142, "distinctness"),
   (1143, "distinctness"), (1144, "distinctness"), (1145, "distinctness"), (1146, "distinctness"),
   (1147, "distinctness"), (1148, "distinctness"), (1149, "distinctness"), (1150, "distinctness"),
   (1151, "distinctness"), (1152, "distinctness"), (1153, "distinctness"), (1154, "distinctness"),
   (1155, "distinctness"), (1156, "distinctness"), (1157, "distinctness"), (1158, "distinctness"),
   (1159, "distinctness"), (1160, "distinctness"), (1161, "distinctness"), (1162, "distinctness"),
   (1163, "distinctness"), (1164, "distinctness"), (1165, "distinctness"),
   (1166, "constructor functional"), (1167, "distinctness"), (1168, "distinctness"),
   (1169, "distinctness"), (1170, "distinctness"), (1171, "distinctness"), (1172, "distinctness"),
   (1173, "distinctness"), (1174, "distinctness"), (1175, "distinctness"), (1176, "distinctness"),
   (1177, "distinctness"), (1178, "distinctness"), (1179, "distinctness"), (1180, "distinctness"),
   (1181, "distinctness"), (1182, "distinctness"), (1183, "distinctness"), (1184, "distinctness"),
   (1185, "distinctness"), (1186, "distinctness"), (1187, "distinctness"), (1188, "distinctness"),
   (1189, "distinctness"), (1190, "distinctness"), (1191, "distinctness"), (1192, "distinctness"),
   (1193, "distinctness"), (1194, "distinctness"), (1195, "distinctness"), (1196, "distinctness"),
   (1197, "distinctness"), (1198, "distinctness"), (1199, "distinctness"), (1200, "distinctness"),
   (1201, "distinctness"), (1202, "distinctness"), (1203, "distinctness"), (1204, "distinctness"),
   (1205, "distinctness"), (1206, "distinctness"), (1207, "distinctness"), (1208, "distinctness"),
   (1209, "distinctness"), (1210, "distinctness"), (1211, "distinctness"), (1212, "distinctness"),
   (1213, "distinctness"), (1214, "distinctness"), (1215, "distinctness"), (1216, "distinctness"),
   (1217, "distinctness"), (1218, "distinctness"), (1219, "constructor functional"),
   (1220, "distinctness"), (1221, "distinctness"), (1222, "distinctness"), (1223, "distinctness"),
   (1224, "distinctness"), (1225, "distinctness"), (1226, "distinctness"), (1227, "distinctness"),
   (1228, "distinctness"), (1229, "distinctness"), (1230, "distinctness"), (1231, "distinctness"),
   (1232, "distinctness"), (1233, "distinctness"), (1234, "distinctness"), (1235, "distinctness"),
   (1236, "distinctness"), (1237, "distinctness"), (1238, "distinctness"), (1239, "distinctness"),
   (1240, "distinctness"), (1241, "distinctness"), (1242, "distinctness"), (1243, "distinctness"),
   (1244, "distinctness"), (1245, "distinctness"), (1246, "distinctness"), (1247, "distinctness"),
   (1248, "distinctness"), (1249, "distinctness"), (1250, "distinctness"), (1251, "distinctness"),
   (1252, "distinctness"), (1253, "distinctness"), (1254, "distinctness"), (1255, "distinctness"),
   (1256, "distinctness"), (1257, "distinctness"), (1258, "distinctness"), (1259, "distinctness"),
   (1260, "distinctness"), (1261, "distinctness"), (1262, "distinctness"), (1263, "distinctness"),
   (1264, "distinctness"), (1265, "distinctness"), (1266, "distinctness"), (1267, "distinctness"),
   (1268, "distinctness"), (1269, "distinctness"), (1270, "distinctness"),
   (1271, "constructor functional"), (1272, "distinctness"), (1273, "distinctness"),
   (1274, "distinctness"), (1275, "distinctness"), (1276, "distinctness"), (1277, "distinctness"),
   (1278, "distinctness"), (1279, "distinctness"), (1280, "distinctness"), (1281, "distinctness"),
   (1282, "distinctness"), (1283, "distinctness"), (1284, "distinctness"), (1285, "distinctness"),
   (1286, "distinctness"), (1287, "distinctness"), (1288, "distinctness"), (1289, "distinctness"),
   (1290, "distinctness"), (1291, "distinctness"), (1292, "distinctness"), (1293, "distinctness"),
   (1294, "distinctness"), (1295, "distinctness"), (1296, "distinctness"), (1297, "distinctness"),
   (1298, "distinctness"), (1299, "distinctness"), (1300, "distinctness"), (1301, "distinctness"),
   (1302, "distinctness"), (1303, "distinctness"), (1304, "distinctness"), (1305, "distinctness"),
   (1306, "distinctness"), (1307, "distinctness"), (1308, "distinctness"), (1309, "distinctness"),
   (1310, "distinctness"), (1311, "distinctness"), (1312, "distinctness"), (1313, "distinctness"),
   (1314, "distinctness"), (1315, "distinctness"), (1316, "distinctness"), (1317, "distinctness"),
   (1318, "distinctness"), (1319, "distinctness"), (1320, "distinctness"), (1321, "distinctness"),
   (1322, "constructor functional"), (1323, "distinctness"), (1324, "distinctness"),
   (1325, "distinctness"), (1326, "distinctness"), (1327, "distinctness"), (1328, "distinctness"),
   (1329, "distinctness"), (1330, "distinctness"), (1331, "distinctness"), (1332, "distinctness"),
   (1333, "distinctness"), (1334, "distinctness"), (1335, "distinctness"), (1336, "distinctness"),
   (1337, "distinctness"), (1338, "distinctness"), (1339, "distinctness"), (1340, "distinctness"),
   (1341, "distinctness"), (1342, "distinctness"), (1343, "distinctness"), (1344, "distinctness"),
   (1345, "distinctness"), (1346, "distinctness"), (1347, "distinctness"), (1348, "distinctness"),
   (1349, "distinctness"), (1350, "distinctness"), (1351, "distinctness"), (1352, "distinctness"),
   (1353, "distinctness"), (1354, "distinctness"), (1355, "distinctness"), (1356, "distinctness"),
   (1357, "distinctness"), (1358, "distinctness"), (1359, "distinctness"), (1360, "distinctness"),
   (1361, "distinctness"), (1362, "distinctness"), (1363, "distinctness"), (1364, "distinctness"),
   (1365, "distinctness"), (1366, "distinctness"), (1367, "distinctness"), (1368, "distinctness"),
   (1369, "distinctness"), (1370, "distinctness"), (1371, "distinctness"),
   (1372, "constructor functional"), (1373, "distinctness"), (1374, "distinctness"),
   (1375, "distinctness"), (1376, "distinctness"), (1377, "distinctness"), (1378, "distinctness"),
   (1379, "distinctness"), (1380, "distinctness"), (1381, "distinctness"), (1382, "distinctness"),
   (1383, "distinctness"), (1384, "distinctness"), (1385, "distinctness"), (1386, "distinctness"),
   (1387, "distinctness"), (1388, "distinctness"), (1389, "distinctness"), (1390, "distinctness"),
   (1391, "distinctness"), (1392, "distinctness"), (1393, "distinctness"), (1394, "distinctness"),
   (1395, "distinctness"), (1396, "distinctness"), (1397, "distinctness"), (1398, "distinctness"),
   (1399, "distinctness"), (1400, "distinctness"), (1401, "distinctness"), (1402, "distinctness"),
   (1403, "distinctness"), (1404, "distinctness"), (1405, "distinctness"), (1406, "distinctness"),
   (1407, "distinctness"), (1408, "distinctness"), (1409, "distinctness"), (1410, "distinctness"),
   (1411, "distinctness"), (1412, "distinctness"), (1413, "distinctness"), (1414, "distinctness"),
   (1415, "distinctness"), (1416, "distinctness"), (1417, "distinctness"), (1418, "distinctness"),
   (1419, "distinctness"), (1420, "distinctness"), (1421, "constructor functional"),
   (1422, "distinctness"), (1423, "distinctness"), (1424, "distinctness"), (1425, "distinctness"),
   (1426, "distinctness"), (1427, "distinctness"), (1428, "distinctness"), (1429, "distinctness"),
   (1430, "distinctness"), (1431, "distinctness"), (1432, "distinctness"), (1433, "distinctness"),
   (1434, "distinctness"), (1435, "distinctness"), (1436, "distinctness"), (1437, "distinctness"),
   (1438, "distinctness"), (1439, "distinctness"), (1440, "distinctness"), (1441, "distinctness"),
   (1442, "distinctness"), (1443, "distinctness"), (1444, "distinctness"), (1445, "distinctness"),
   (1446, "distinctness"), (1447, "distinctness"), (1448, "distinctness"), (1449, "distinctness"),
   (1450, "distinctness"), (1451, "distinctness"), (1452, "distinctness"), (1453, "distinctness"),
   (1454, "distinctness"), (1455, "distinctness"), (1456, "distinctness"), (1457, "distinctness"),
   (1458, "distinctness"), (1459, "distinctness"), (1460, "distinctness"), (1461, "distinctness"),
   (1462, "distinctness"), (1463, "distinctness"), (1464, "distinctness"), (1465, "distinctness"),
   (1466, "distinctness"), (1467, "distinctness"), (1468, "distinctness"),
   (1469, "constructor functional"), (1470, "distinctness"), (1471, "distinctness"),
   (1472, "distinctness"), (1473, "distinctness"), (1474, "distinctness"), (1475, "distinctness"),
   (1476, "distinctness"), (1477, "distinctness"), (1478, "distinctness"), (1479, "distinctness"),
   (1480, "distinctness"), (1481, "distinctness"), (1482, "distinctness"), (1483, "distinctness"),
   (1484, "distinctness"), (1485, "distinctness"), (1486, "distinctness"), (1487, "distinctness"),
   (1488, "distinctness"), (1489, "distinctness"), (1490, "distinctness"), (1491, "distinctness"),
   (1492, "distinctness"), (1493, "distinctness"), (1494, "distinctness"), (1495, "distinctness"),
   (1496, "distinctness"), (1497, "distinctness"), (1498, "distinctness"), (1499, "distinctness"),
   (1500, "distinctness"), (1501, "distinctness"), (1502, "distinctness"), (1503, "distinctness"),
   (1504, "distinctness"), (1505, "distinctness"), (1506, "distinctness"), (1507, "distinctness"),
   (1508, "distinctness"), (1509, "distinctness"), (1510, "distinctness"), (1511, "distinctness"),
   (1512, "distinctness"), (1513, "distinctness"), (1514, "distinctness"), (1515, "distinctness"),
   (1516, "constructor functional"), (1517, "distinctness"), (1518, "distinctness"),
   (1519, "distinctness"), (1520, "distinctness"), (1521, "distinctness"), (1522, "distinctness"),
   (1523, "distinctness"), (1524, "distinctness"), (1525, "distinctness"), (1526, "distinctness"),
   (1527, "distinctness"), (1528, "distinctness"), (1529, "distinctness"), (1530, "distinctness"),
   (1531, "distinctness"), (1532, "distinctness"), (1533, "distinctness"), (1534, "distinctness"),
   (1535, "distinctness"), (1536, "distinctness"), (1537, "distinctness"), (1538, "distinctness"),
   (1539, "distinctness"), (1540, "distinctness"), (1541, "distinctness"), (1542, "distinctness"),
   (1543, "distinctness"), (1544, "distinctness"), (1545, "distinctness"), (1546, "distinctness"),
   (1547, "distinctness"), (1548, "distinctness"), (1549, "distinctness"), (1550, "distinctness"),
   (1551, "distinctness"), (1552, "distinctness"), (1553, "distinctness"), (1554, "distinctness"),
   (1555, "distinctness"), (1556, "distinctness"), (1557, "distinctness"), (1558, "distinctness"),
   (1559, "distinctness"), (1560, "distinctness"), (1561, "distinctness"),
   (1562, "constructor functional"), (1563, "distinctness"), (1564, "distinctness"),
   (1565, "distinctness"), (1566, "distinctness"), (1567, "distinctness"), (1568, "distinctness"),
   (1569, "distinctness"), (1570, "distinctness"), (1571, "distinctness"), (1572, "distinctness"),
   (1573, "distinctness"), (1574, "distinctness"), (1575, "distinctness"), (1576, "distinctness"),
   (1577, "distinctness"), (1578, "distinctness"), (1579, "distinctness"), (1580, "distinctness"),
   (1581, "distinctness"), (1582, "distinctness"), (1583, "distinctness"), (1584, "distinctness"),
   (1585, "distinctness"), (1586, "distinctness"), (1587, "distinctness"), (1588, "distinctness"),
   (1589, "distinctness"), (1590, "distinctness"), (1591, "distinctness"), (1592, "distinctness"),
   (1593, "distinctness"), (1594, "distinctness"), (1595, "distinctness"), (1596, "distinctness"),
   (1597, "distinctness"), (1598, "distinctness"), (1599, "distinctness"), (1600, "distinctness"),
   (1601, "distinctness"), (1602, "distinctness"), (1603, "distinctness"), (1604, "distinctness"),
   (1605, "distinctness"), (1606, "distinctness"), (1607, "constructor functional"),
   (1608, "distinctness"), (1609, "distinctness"), (1610, "distinctness"), (1611, "distinctness"),
   (1612, "distinctness"), (1613, "distinctness"), (1614, "distinctness"), (1615, "distinctness"),
   (1616, "distinctness"), (1617, "distinctness"), (1618, "distinctness"), (1619, "distinctness"),
   (1620, "distinctness"), (1621, "distinctness"), (1622, "distinctness"), (1623, "distinctness"),
   (1624, "distinctness"), (1625, "distinctness"), (1626, "distinctness"), (1627, "distinctness"),
   (1628, "distinctness"), (1629, "distinctness"), (1630, "distinctness"), (1631, "distinctness"),
   (1632, "distinctness"), (1633, "distinctness"), (1634, "distinctness"), (1635, "distinctness"),
   (1636, "distinctness"), (1637, "distinctness"), (1638, "distinctness"), (1639, "distinctness"),
   (1640, "distinctness"), (1641, "distinctness"), (1642, "distinctness"), (1643, "distinctness"),
   (1644, "distinctness"), (1645, "distinctness"), (1646, "distinctness"), (1647, "distinctness"),
   (1648, "distinctness"), (1649, "distinctness"), (1650, "distinctness"),
   (1651, "constructor functional"), (1652, "distinctness"), (1653, "distinctness"),
   (1654, "distinctness"), (1655, "distinctness"), (1656, "distinctness"), (1657, "distinctness"),
   (1658, "distinctness"), (1659, "distinctness"), (1660, "distinctness"), (1661, "distinctness"),
   (1662, "distinctness"), (1663, "distinctness"), (1664, "distinctness"), (1665, "distinctness"),
   (1666, "distinctness"), (1667, "distinctness"), (1668, "distinctness"), (1669, "distinctness"),
   (1670, "distinctness"), (1671, "distinctness"), (1672, "distinctness"), (1673, "distinctness"),
   (1674, "distinctness"), (1675, "distinctness"), (1676, "distinctness"), (1677, "distinctness"),
   (1678, "distinctness"), (1679, "distinctness"), (1680, "distinctness"), (1681, "distinctness"),
   (1682, "distinctness"), (1683, "distinctness"), (1684, "distinctness"), (1685, "distinctness"),
   (1686, "distinctness"), (1687, "distinctness"), (1688, "distinctness"), (1689, "distinctness"),
   (1690, "distinctness"), (1691, "distinctness"), (1692, "distinctness"), (1693, "distinctness"),
   (1694, "constructor functional"), (1695, "distinctness"), (1696, "distinctness"),
   (1697, "distinctness"), (1698, "distinctness"), (1699, "distinctness"), (1700, "distinctness"),
   (1701, "distinctness"), (1702, "distinctness"), (1703, "distinctness"), (1704, "distinctness"),
   (1705, "distinctness"), (1706, "distinctness"), (1707, "distinctness"), (1708, "distinctness"),
   (1709, "distinctness"), (1710, "distinctness"), (1711, "distinctness"), (1712, "distinctness"),
   (1713, "distinctness"), (1714, "distinctness"), (1715, "distinctness"), (1716, "distinctness"),
   (1717, "distinctness"), (1718, "distinctness"), (1719, "distinctness"), (1720, "distinctness"),
   (1721, "distinctness"), (1722, "distinctness"), (1723, "distinctness"), (1724, "distinctness"),
   (1725, "distinctness"), (1726, "distinctness"), (1727, "distinctness"), (1728, "distinctness"),
   (1729, "distinctness"), (1730, "distinctness"), (1731, "distinctness"), (1732, "distinctness"),
   (1733, "distinctness"), (1734, "distinctness"), (1735, "distinctness"),
   (1736, "constructor functional"), (1737, "distinctness"), (1738, "distinctness"),
   (1739, "distinctness"), (1740, "distinctness"), (1741, "distinctness"), (1742, "distinctness"),
   (1743, "distinctness"), (1744, "distinctness"), (1745, "distinctness"), (1746, "distinctness"),
   (1747, "distinctness"), (1748, "distinctness"), (1749, "distinctness"), (1750, "distinctness"),
   (1751, "distinctness"), (1752, "distinctness"), (1753, "distinctness"), (1754, "distinctness"),
   (1755, "distinctness"), (1756, "distinctness"), (1757, "distinctness"), (1758, "distinctness"),
   (1759, "distinctness"), (1760, "distinctness"), (1761, "distinctness"), (1762, "distinctness"),
   (1763, "distinctness"), (1764, "distinctness"), (1765, "distinctness"), (1766, "distinctness"),
   (1767, "distinctness"), (1768, "distinctness"), (1769, "distinctness"), (1770, "distinctness"),
   (1771, "distinctness"), (1772, "distinctness"), (1773, "distinctness"), (1774, "distinctness"),
   (1775, "distinctness"), (1776, "distinctness"), (1777, "constructor functional"),
   (1778, "distinctness"), (1779, "distinctness"), (1780, "distinctness"), (1781, "distinctness"),
   (1782, "distinctness"), (1783, "distinctness"), (1784, "distinctness"), (1785, "distinctness"),
   (1786, "distinctness"), (1787, "distinctness"), (1788, "distinctness"), (1789, "distinctness"),
   (1790, "distinctness"), (1791, "distinctness"), (1792, "distinctness"), (1793, "distinctness"),
   (1794, "distinctness"), (1795, "distinctness"), (1796, "distinctness"), (1797, "distinctness"),
   (1798, "distinctness"), (1799, "distinctness"), (1800, "distinctness"), (1801, "distinctness"),
   (1802, "distinctness"), (1803, "distinctness"), (1804, "distinctness"), (1805, "distinctness"),
   (1806, "distinctness"), (1807, "distinctness"), (1808, "distinctness"), (1809, "distinctness"),
   (1810, "distinctness"), (1811, "distinctness"), (1812, "distinctness"), (1813, "distinctness"),
   (1814, "distinctness"), (1815, "distinctness"), (1816, "distinctness"),
   (1817, "constructor functional"), (1818, "distinctness"), (1819, "distinctness"),
   (1820, "distinctness"), (1821, "distinctness"), (1822, "distinctness"), (1823, "distinctness"),
   (1824, "distinctness"), (1825, "distinctness"), (1826, "distinctness"), (1827, "distinctness"),
   (1828, "distinctness"), (1829, "distinctness"), (1830, "distinctness"), (1831, "distinctness"),
   (1832, "distinctness"), (1833, "distinctness"), (1834, "distinctness"), (1835, "distinctness"),
   (1836, "distinctness"), (1837, "distinctness"), (1838, "distinctness"), (1839, "distinctness"),
   (1840, "distinctness"), (1841, "distinctness"), (1842, "distinctness"), (1843, "distinctness"),
   (1844, "distinctness"), (1845, "distinctness"), (1846, "distinctness"), (1847, "distinctness"),
   (1848, "distinctness"), (1849, "distinctness"), (1850, "distinctness"), (1851, "distinctness"),
   (1852, "distinctness"), (1853, "distinctness"), (1854, "distinctness"), (1855, "distinctness"),
   (1856, "constructor functional"), (1857, "distinctness"), (1858, "distinctness"),
   (1859, "distinctness"), (1860, "distinctness"), (1861, "distinctness"), (1862, "distinctness"),
   (1863, "distinctness"), (1864, "distinctness"), (1865, "distinctness"), (1866, "distinctness"),
   (1867, "distinctness"), (1868, "distinctness"), (1869, "distinctness"), (1870, "distinctness"),
   (1871, "distinctness"), (1872, "distinctness"), (1873, "distinctness"), (1874, "distinctness"),
   (1875, "distinctness"), (1876, "distinctness"), (1877, "distinctness"), (1878, "distinctness"),
   (1879, "distinctness"), (1880, "distinctness"), (1881, "distinctness"), (1882, "distinctness"),
   (1883, "distinctness"), (1884, "distinctness"), (1885, "distinctness"), (1886, "distinctness"),
   (1887, "distinctness"), (1888, "distinctness"), (1889, "distinctness"), (1890, "distinctness"),
   (1891, "distinctness"), (1892, "distinctness"), (1893, "distinctness"),
   (1894, "constructor functional"), (1895, "distinctness"), (1896, "distinctness"),
   (1897, "distinctness"), (1898, "distinctness"), (1899, "distinctness"), (1900, "distinctness"),
   (1901, "distinctness"), (1902, "distinctness"), (1903, "distinctness"), (1904, "distinctness"),
   (1905, "distinctness"), (1906, "distinctness"), (1907, "distinctness"), (1908, "distinctness"),
   (1909, "distinctness"), (1910, "distinctness"), (1911, "distinctness"), (1912, "distinctness"),
   (1913, "distinctness"), (1914, "distinctness"), (1915, "distinctness"), (1916, "distinctness"),
   (1917, "distinctness"), (1918, "distinctness"), (1919, "distinctness"), (1920, "distinctness"),
   (1921, "distinctness"), (1922, "distinctness"), (1923, "distinctness"), (1924, "distinctness"),
   (1925, "distinctness"), (1926, "distinctness"), (1927, "distinctness"), (1928, "distinctness"),
   (1929, "distinctness"), (1930, "distinctness"), (1931, "constructor functional"),
   (1932, "distinctness"), (1933, "distinctness"), (1934, "distinctness"), (1935, "distinctness"),
   (1936, "distinctness"), (1937, "distinctness"), (1938, "distinctness"), (1939, "distinctness"),
   (1940, "distinctness"), (1941, "distinctness"), (1942, "distinctness"), (1943, "distinctness"),
   (1944, "distinctness"), (1945, "distinctness"), (1946, "distinctness"), (1947, "distinctness"),
   (1948, "distinctness"), (1949, "distinctness"), (1950, "distinctness"), (1951, "distinctness"),
   (1952, "distinctness"), (1953, "distinctness"), (1954, "distinctness"), (1955, "distinctness"),
   (1956, "distinctness"), (1957, "distinctness"), (1958, "distinctness"), (1959, "distinctness"),
   (1960, "distinctness"), (1961, "distinctness"), (1962, "distinctness"), (1963, "distinctness"),
   (1964, "distinctness"), (1965, "distinctness"), (1966, "distinctness"),
   (1967, "constructor functional"), (1968, "distinctness"), (1969, "distinctness"),
   (1970, "distinctness"), (1971, "distinctness"), (1972, "distinctness"), (1973, "distinctness"),
   (1974, "distinctness"), (1975, "distinctness"), (1976, "distinctness"), (1977, "distinctness"),
   (1978, "distinctness"), (1979, "distinctness"), (1980, "distinctness"), (1981, "distinctness"),
   (1982, "distinctness"), (1983, "distinctness"), (1984, "distinctness"), (1985, "distinctness"),
   (1986, "distinctness"), (1987, "distinctness"), (1988, "distinctness"), (1989, "distinctness"),
   (1990, "distinctness"), (1991, "distinctness"), (1992, "distinctness"), (1993, "distinctness"),
   (1994, "distinctness"), (1995, "distinctness"), (1996, "distinctness"), (1997, "distinctness"),
   (1998, "distinctness"), (1999, "distinctness"), (2000, "distinctness"), (2001, "distinctness"),
   (2002, "constructor functional"), (2003, "distinctness"), (2004, "distinctness"),
   (2005, "distinctness"), (2006, "distinctness"), (2007, "distinctness"), (2008, "distinctness"),
   (2009, "distinctness"), (2010, "distinctness"), (2011, "distinctness"), (2012, "distinctness"),
   (2013, "distinctness"), (2014, "distinctness"), (2015, "distinctness"), (2016, "distinctness"),
   (2017, "distinctness"), (2018, "distinctness"), (2019, "distinctness"), (2020, "distinctness"),
   (2021, "distinctness"), (2022, "distinctness"), (2023, "distinctness"), (2024, "distinctness"),
   (2025, "distinctness"), (2026, "distinctness"), (2027, "distinctness"), (2028, "distinctness"),
   (2029, "distinctness"), (2030, "distinctness"), (2031, "distinctness"), (2032, "distinctness"),
   (2033, "distinctness"), (2034, "distinctness"), (2035, "distinctness"),
   (2036, "constructor functional"), (2037, "distinctness"), (2038, "distinctness"),
   (2039, "distinctness"), (2040, "distinctness"), (2041, "distinctness"), (2042, "distinctness"),
   (2043, "distinctness"), (2044, "distinctness"), (2045, "distinctness"), (2046, "distinctness"),
   (2047, "distinctness"), (2048, "distinctness"), (2049, "distinctness"), (2050, "distinctness"),
   (2051, "distinctness"), (2052, "distinctness"), (2053, "distinctness"), (2054, "distinctness"),
   (2055, "distinctness"), (2056, "distinctness"), (2057, "distinctness"), (2058, "distinctness"),
   (2059, "distinctness"), (2060, "distinctness"), (2061, "distinctness"), (2062, "distinctness"),
   (2063, "distinctness"), (2064, "distinctness"), (2065, "distinctness"), (2066, "distinctness"),
   (2067, "distinctness"), (2068, "distinctness"), (2069, "constructor functional"),
   (2070, "distinctness"), (2071, "distinctness"), (2072, "distinctness"), (2073, "distinctness"),
   (2074, "distinctness"), (2075, "distinctness"), (2076, "distinctness"), (2077, "distinctness"),
   (2078, "distinctness"), (2079, "distinctness"), (2080, "distinctness"), (2081, "distinctness"),
   (2082, "distinctness"), (2083, "distinctness"), (2084, "distinctness"), (2085, "distinctness"),
   (2086, "distinctness"), (2087, "distinctness"), (2088, "distinctness"), (2089, "distinctness"),
   (2090, "distinctness"), (2091, "distinctness"), (2092, "distinctness"), (2093, "distinctness"),
   (2094, "distinctness"), (2095, "distinctness"), (2096, "distinctness"), (2097, "distinctness"),
   (2098, "distinctness"), (2099, "distinctness"), (2100, "distinctness"),
   (2101, "constructor functional"), (2102, "distinctness"), (2103, "distinctness"),
   (2104, "distinctness"), (2105, "distinctness"), (2106, "distinctness"), (2107, "distinctness"),
   (2108, "distinctness"), (2109, "distinctness"), (2110, "distinctness"), (2111, "distinctness"),
   (2112, "distinctness"), (2113, "distinctness"), (2114, "distinctness"), (2115, "distinctness"),
   (2116, "distinctness"), (2117, "distinctness"), (2118, "distinctness"), (2119, "distinctness"),
   (2120, "distinctness"), (2121, "distinctness"), (2122, "distinctness"), (2123, "distinctness"),
   (2124, "distinctness"), (2125, "distinctness"), (2126, "distinctness"), (2127, "distinctness"),
   (2128, "distinctness"), (2129, "distinctness"), (2130, "distinctness"), (2131, "distinctness"),
   (2132, "constructor functional"), (2133, "distinctness"), (2134, "distinctness"),
   (2135, "distinctness"), (2136, "distinctness"), (2137, "distinctness"), (2138, "distinctness"),
   (2139, "distinctness"), (2140, "distinctness"), (2141, "distinctness"), (2142, "distinctness"),
   (2143, "distinctness"), (2144, "distinctness"), (2145, "distinctness"), (2146, "distinctness"),
   (2147, "distinctness"), (2148, "distinctness"), (2149, "distinctness"), (2150, "distinctness"),
   (2151, "distinctness"), (2152, "distinctness"), (2153, "distinctness"), (2154, "distinctness"),
   (2155, "distinctness"), (2156, "distinctness"), (2157, "distinctness"), (2158, "distinctness"),
   (2159, "distinctness"), (2160, "distinctness"), (2161, "distinctness"),
   (2162, "constructor functional"), (2163, "distinctness"), (2164, "distinctness"),
   (2165, "distinctness"), (2166, "distinctness"), (2167, "distinctness"), (2168, "distinctness"),
   (2169, "distinctness"), (2170, "distinctness"), (2171, "distinctness"), (2172, "distinctness"),
   (2173, "distinctness"), (2174, "distinctness"), (2175, "distinctness"), (2176, "distinctness"),
   (2177, "distinctness"), (2178, "distinctness"), (2179, "distinctness"), (2180, "distinctness"),
   (2181, "distinctness"), (2182, "distinctness"), (2183, "distinctness"), (2184, "distinctness"),
   (2185, "distinctness"), (2186, "distinctness"), (2187, "distinctness"), (2188, "distinctness"),
   (2189, "distinctness"), (2190, "distinctness"), (2191, "constructor functional"),
   (2192, "distinctness"), (2193, "distinctness"), (2194, "distinctness"), (2195, "distinctness"),
   (2196, "distinctness"), (2197, "distinctness"), (2198, "distinctness"), (2199, "distinctness"),
   (2200, "distinctness"), (2201, "distinctness"), (2202, "distinctness"), (2203, "distinctness"),
   (2204, "distinctness"), (2205, "distinctness"), (2206, "distinctness"), (2207, "distinctness"),
   (2208, "distinctness"), (2209, "distinctness"), (2210, "distinctness"), (2211, "distinctness"),
   (2212, "distinctness"), (2213, "distinctness"), (2214, "distinctness"), (2215, "distinctness"),
   (2216, "distinctness"), (2217, "distinctness"), (2218, "distinctness"),
   (2219, "constructor functional"), (2220, "distinctness"), (2221, "distinctness"),
   (2222, "distinctness"), (2223, "distinctness"), (2224, "distinctness"), (2225, "distinctness"),
   (2226, "distinctness"), (2227, "distinctness"), (2228, "distinctness"), (2229, "distinctness"),
   (2230, "distinctness"), (2231, "distinctness"), (2232, "distinctness"), (2233, "distinctness"),
   (2234, "distinctness"), (2235, "distinctness"), (2236, "distinctness"), (2237, "distinctness"),
   (2238, "distinctness"), (2239, "distinctness"), (2240, "distinctness"), (2241, "distinctness"),
   (2242, "distinctness"), (2243, "distinctness"), (2244, "distinctness"), (2245, "distinctness"),
   (2246, "constructor functional"), (2247, "distinctness"), (2248, "distinctness"),
   (2249, "distinctness"), (2250, "distinctness"), (2251, "distinctness"), (2252, "distinctness"),
   (2253, "distinctness"), (2254, "distinctness"), (2255, "distinctness"), (2256, "distinctness"),
   (2257, "distinctness"), (2258, "distinctness"), (2259, "distinctness"), (2260, "distinctness"),
   (2261, "distinctness"), (2262, "distinctness"), (2263, "distinctness"), (2264, "distinctness"),
   (2265, "distinctness"), (2266, "distinctness"), (2267, "distinctness"), (2268, "distinctness"),
   (2269, "distinctness"), (2270, "distinctness"), (2271, "distinctness"),
   (2272, "constructor functional"), (2273, "distinctness"), (2274, "distinctness"),
   (2275, "distinctness"), (2276, "distinctness"), (2277, "distinctness"), (2278, "distinctness"),
   (2279, "distinctness"), (2280, "distinctness"), (2281, "distinctness"), (2282, "distinctness"),
   (2283, "distinctness"), (2284, "distinctness"), (2285, "distinctness"), (2286, "distinctness"),
   (2287, "distinctness"), (2288, "distinctness"), (2289, "distinctness"), (2290, "distinctness"),
   (2291, "distinctness"), (2292, "distinctness"), (2293, "distinctness"), (2294, "distinctness"),
   (2295, "distinctness"), (2296, "distinctness"), (2297, "constructor functional"),
   (2298, "distinctness"), (2299, "distinctness"), (2300, "distinctness"), (2301, "distinctness"),
   (2302, "distinctness"), (2303, "distinctness"), (2304, "distinctness"), (2305, "distinctness"),
   (2306, "distinctness"), (2307, "distinctness"), (2308, "distinctness"), (2309, "distinctness"),
   (2310, "distinctness"), (2311, "distinctness"), (2312, "distinctness"), (2313, "distinctness"),
   (2314, "distinctness"), (2315, "distinctness"), (2316, "distinctness"), (2317, "distinctness"),
   (2318, "distinctness"), (2319, "distinctness"), (2320, "distinctness"),
   (2321, "constructor functional"), (2322, "distinctness"), (2323, "distinctness"),
   (2324, "distinctness"), (2325, "distinctness"), (2326, "distinctness"), (2327, "distinctness"),
   (2328, "distinctness"), (2329, "distinctness"), (2330, "distinctness"), (2331, "distinctness"),
   (2332, "distinctness"), (2333, "distinctness"), (2334, "distinctness"), (2335, "distinctness"),
   (2336, "distinctness"), (2337, "distinctness"), (2338, "distinctness"), (2339, "distinctness"),
   (2340, "distinctness"), (2341, "distinctness"), (2342, "distinctness"), (2343, "distinctness"),
   (2344, "constructor functional"), (2345, "distinctness"), (2346, "distinctness"),
   (2347, "distinctness"), (2348, "distinctness"), (2349, "distinctness"), (2350, "distinctness"),
   (2351, "distinctness"), (2352, "distinctness"), (2353, "distinctness"), (2354, "distinctness"),
   (2355, "distinctness"), (2356, "distinctness"), (2357, "distinctness"), (2358, "distinctness"),
   (2359, "distinctness"), (2360, "distinctness"), (2361, "distinctness"), (2362, "distinctness"),
   (2363, "distinctness"), (2364, "distinctness"), (2365, "distinctness"),
   (2366, "constructor functional"), (2367, "distinctness"), (2368, "distinctness"),
   (2369, "distinctness"), (2370, "distinctness"), (2371, "distinctness"), (2372, "distinctness"),
   (2373, "distinctness"), (2374, "distinctness"), (2375, "distinctness"), (2376, "distinctness"),
   (2377, "distinctness"), (2378, "distinctness"), (2379, "distinctness"), (2380, "distinctness"),
   (2381, "distinctness"), (2382, "distinctness"), (2383, "distinctness"), (2384, "distinctness"),
   (2385, "distinctness"), (2386, "distinctness"), (2387, "constructor functional"),
   (2388, "distinctness"), (2389, "distinctness"), (2390, "distinctness"), (2391, "distinctness"),
   (2392, "distinctness"), (2393, "distinctness"), (2394, "distinctness"), (2395, "distinctness"),
   (2396, "distinctness"), (2397, "distinctness"), (2398, "distinctness"), (2399, "distinctness"),
   (2400, "distinctness"), (2401, "distinctness"), (2402, "distinctness"), (2403, "distinctness"),
   (2404, "distinctness"), (2405, "distinctness"), (2406, "distinctness"),
   (2407, "constructor functional"), (2408, "distinctness"), (2409, "distinctness"),
   (2410, "distinctness"), (2411, "distinctness"), (2412, "distinctness"), (2413, "distinctness"),
   (2414, "distinctness"), (2415, "distinctness"), (2416, "distinctness"), (2417, "distinctness"),
   (2418, "distinctness"), (2419, "distinctness"), (2420, "distinctness"), (2421, "distinctness"),
   (2422, "distinctness"), (2423, "distinctness"), (2424, "distinctness"), (2425, "distinctness"),
   (2426, "constructor functional"), (2427, "distinctness"), (2428, "distinctness"),
   (2429, "distinctness"), (2430, "distinctness"), (2431, "distinctness"), (2432, "distinctness"),
   (2433, "distinctness"), (2434, "distinctness"), (2435, "distinctness"), (2436, "distinctness"),
   (2437, "distinctness"), (2438, "distinctness"), (2439, "distinctness"), (2440, "distinctness"),
   (2441, "distinctness"), (2442, "distinctness"), (2443, "distinctness"),
   (2444, "constructor functional"), (2445, "distinctness"), (2446, "distinctness"),
   (2447, "distinctness"), (2448, "distinctness"), (2449, "distinctness"), (2450, "distinctness"),
   (2451, "distinctness"), (2452, "distinctness"), (2453, "distinctness"), (2454, "distinctness"),
   (2455, "distinctness"), (2456, "distinctness"), (2457, "distinctness"), (2458, "distinctness"),
   (2459, "distinctness"), (2460, "distinctness"), (2461, "constructor functional"),
   (2462, "distinctness"), (2463, "distinctness"), (2464, "distinctness"), (2465, "distinctness"),
   (2466, "distinctness"), (2467, "distinctness"), (2468, "distinctness"), (2469, "distinctness"),
   (2470, "distinctness"), (2471, "distinctness"), (2472, "distinctness"), (2473, "distinctness"),
   (2474, "distinctness"), (2475, "distinctness"), (2476, "distinctness"),
   (2477, "constructor functional"), (2478, "distinctness"), (2479, "distinctness"),
   (2480, "distinctness"), (2481, "distinctness"), (2482, "distinctness"), (2483, "distinctness"),
   (2484, "distinctness"), (2485, "distinctness"), (2486, "distinctness"), (2487, "distinctness"),
   (2488, "distinctness"), (2489, "distinctness"), (2490, "distinctness"), (2491, "distinctness"),
   (2492, "constructor functional"), (2493, "distinctness"), (2494, "distinctness"),
   (2495, "distinctness"), (2496, "distinctness"), (2497, "distinctness"), (2498, "distinctness"),
   (2499, "distinctness"), (2500, "distinctness"), (2501, "distinctness"), (2502, "distinctness"),
   (2503, "distinctness"), (2504, "distinctness"), (2505, "distinctness"),
   (2506, "constructor functional"), (2507, "distinctness"), (2508, "distinctness"),
   (2509, "distinctness"), (2510, "distinctness"), (2511, "distinctness"), (2512, "distinctness"),
   (2513, "distinctness"), (2514, "distinctness"), (2515, "distinctness"), (2516, "distinctness"),
   (2517, "distinctness"), (2518, "distinctness"), (2519, "constructor functional"),
   (2520, "distinctness"), (2521, "distinctness"), (2522, "distinctness"), (2523, "distinctness"),
   (2524, "distinctness"), (2525, "distinctness"), (2526, "distinctness"), (2527, "distinctness"),
   (2528, "distinctness"), (2529, "distinctness"), (2530, "distinctness"),
   (2531, "constructor functional"), (2532, "distinctness"), (2533, "distinctness"),
   (2534, "distinctness"), (2535, "distinctness"), (2536, "distinctness"), (2537, "distinctness"),
   (2538, "distinctness"), (2539, "distinctness"), (2540, "distinctness"), (2541, "distinctness"),
   (2542, "constructor functional"), (2543, "distinctness"), (2544, "distinctness"),
   (2545, "distinctness"), (2546, "distinctness"), (2547, "distinctness"), (2548, "distinctness"),
   (2549, "distinctness"), (2550, "distinctness"), (2551, "distinctness"),
   (2552, "constructor functional"), (2553, "distinctness"), (2554, "distinctness"),
   (2555, "distinctness"), (2556, "distinctness"), (2557, "distinctness"), (2558, "distinctness"),
   (2559, "distinctness"), (2560, "distinctness"), (2561, "constructor functional"),
   (2562, "distinctness"), (2563, "distinctness"), (2564, "distinctness"), (2565, "distinctness"),
   (2566, "distinctness"), (2567, "distinctness"), (2568, "distinctness"),
   (2569, "constructor functional"), (2570, "distinctness"), (2571, "distinctness"),
   (2572, "distinctness"), (2573, "distinctness"), (2574, "distinctness"), (2575, "distinctness"),
   (2576, "constructor functional"), (2577, "distinctness"), (2578, "distinctness"),
   (2579, "distinctness"), (2580, "distinctness"), (2581, "distinctness"),
   (2582, "constructor functional"), (2583, "distinctness"), (2584, "distinctness"),
   (2585, "distinctness"), (2586, "distinctness"), (2587, "constructor functional"),
   (2588, "distinctness"), (2589, "distinctness"), (2590, "distinctness"),
   (2591, "constructor functional"), (2592, "distinctness"), (2593, "distinctness"),
   (2594, "constructor functional"), (2595, "injectivity"), (2596, "distinctness"),
   (2597, "distinctness"), (2598, "distinctness"), (2599, "constructor functional"),
   (2600, "injectivity"), (2601, "distinctness"), (2602, "distinctness"), (2603, "no direction"),
   (2604, "no direction"), (2605, "constructor functional"), (2606, "injectivity"),
   (2607, "distinctness"), (2608, "constructor functional"), (2609, "injectivity"),
   (2610, "distinctness"), (2611, "constructor functional"), (2612, "injectivity"),
   (2613, "no direction"), (2614, "no direction"), (2615, "no direction"), (2616, "no direction"),
   (2617, "constructor functional"), (2618, "injectivity"), (2619, "constructor functional"),
   (2620, "injectivity"), (2621, "no direction"), (2622, "no direction"),
   (2623, "constructor functional"), (2624, "injectivity"), (2630, "constructor functional"),
   (2631, "injectivity"), (2632, "constructor functional"), (2633, "injectivity"),
   (2634, "constructor functional"), (2635, "injectivity"), (2638, "constructor functional"),
   (2639, "injectivity"), (2640, "constructor functional"), (2641, "injectivity"),
   (2642, "constructor functional"), (2643, "injectivity"), (2644, "hooked functional"),
   (2645, "parameter functional"), (2646, "hooked functional"), (2656, "hooked functional"),
   (2662, "hooked functional"), (2664, "hooked functional"), (2668, "hooked functional"),
   (2672, "hooked functional"), (2674, "hooked functional"), (2676, "hooked functional"),
   (2701, "constructor functional"), (2703, "hooked functional"), (2708, "function functional"),
   (2709, "function functional"), (2714, "function functional"), (2715, "function functional"),
   (2716, "function functional"), (2717, "function functional"), (2718, "function functional"),
   (2719, "function functional"), (2728, "function functional"), (2729, "function functional"),
   (2731, "function functional"), (2732, "function functional"), (2733, "function functional"),
   (2734, "function functional"), (2735, "function functional"), (2738, "hooked functional"),
   (2742, "constructor functional"), (2744, "constructor functional"),
   (2745, "constructor functional"), (2749, "hooked functional"), (2750, "hooked functional"),
   (2754, "hooked functional"), (2758, "no junk"), (2759, "no junk"), (2762, "no junk"),
   (2763, "no junk"), (2764, "no junk"), (2765, "no junk"), (2766, "no junk"), (2767, "no junk"),
   (2768, "no junk"), (2769, "no junk"), (2774, "no junk"), (2775, "no junk"), (2776, "no junk"),
   (2777, "no junk"), (2778, "no junk"), (2779, "no junk"), (2780, "no junk"), (2781, "no junk"),
   (2811, "no direction"), (2813, "no direction"), (2814, "no direction"), (2815, "rewrite rule"),
   (2816, "rewrite rule"), (2817, "rewrite rule"), (2818, "rewrite rule"), (2819, "rewrite rule"),
   (2820, "rewrite rule"), (2821, "rewrite rule"), (2822, "rewrite rule"), (2823, "library"),
   (2824, "library"), (2825, "library"), (2826, "library"), (2844, "library"), (2848, "library"),
   (2851, "library"), (2852, "library"), (2855, "library"), (2885, "library"), (2886, "library"),
   (2887, "no direction"), (2888, "library"), (2890, "no direction"), (2891, "no direction"),
   (2892, "no direction"), (2893, "no direction"), (2894, "no direction"), (2895, "no direction"),
   (2896, "no direction"), (2899, "function equation"), (2900, "function equation"),
   (2901, "function equation"), (2902, "function equation"), (2911, "function equation"),
   (2912, "function equation"), (2913, "function equation"), (2914, "function equation"),
   (2915, "function equation"), (2916, "function equation"), (2917, "function equation"),
   (2918, "function equation"), (2919, "function equation"), (2920, "function equation"),
   (2921, "function equation"), (2922, "function equation"), (2938, "function equation"),
   (2939, "function equation"), (2940, "function equation"), (2941, "function equation"),
   (2944, "function equation"), (2945, "function equation"), (2946, "function equation"),
   (2947, "function equation"), (2948, "function equation"), (2949, "function equation"),
   (2950, "function equation"), (2951, "function equation"), (2952, "function equation"),
   (2953, "function equation"), (2960, "no direction"), (2961, "no direction"),
   (2962, "no direction"), (2964, "no direction"), (2965, "no direction"), (2970, "no direction"),
   (2971, "no direction"), (2972, "no direction"), (2973, "no direction"), (2974, "no direction"),
   (2975, "no direction"), (2976, "function equation"), (2983, "no direction"),
   (2984, "no direction"), (2986, "no direction"), (2987, "no direction"), (2988, "no direction"),
   (2989, "no direction"), (2990, "no direction"), (2992, "library"), (2993, "library"),
   (2994, "library"), (2995, "library"), (2996, "library"), (2997, "library"), (2998, "library")]

/-- The sentences of a class with a theorem in the tie that no theorem of this file holds of: the
tie's remainder on this text. -/
def uncovered : List (Nat × String) :=
  []

/-- Each listed sentence's class is a class of the account. -/
theorem lists_classes : (unmapped ++ uncovered).all (fun ic => (classes.map (·.1)).contains ic.2) = true := by
  decide +kernel

/-- For each class of the account, the listed sentences of it, in their order, are a sublist of its
indices: one pass over each class's list. -/
theorem lists_sub : (classes.map (·.1)).all (fun n =>
    (((unmapped ++ uncovered).filter (·.2 == n)).map (·.1)).isSublist (classOf n)) = true := by
  decide +kernel

/-- Each listed sentence is in its class in the account (`tieAll_of_groups`). -/
theorem lists_in_account : (unmapped ++ uncovered).all (fun ic => (classOf ic.2).contains ic.1) = true :=
  tieAll_of_groups lists_classes lists_sub

/-! ## Γ's symbol names, as a literal -/

/-- Γ's symbol names (`c.symName` of each of `kernelSyms c`, in its order), each as its code
(`KoreAML.Distinct.strCode`), written out. -/
def gSymCodes : List Nat :=
  [6197441387, 6097760100, 100987944911744851354065855052,
   35480656676607336660446062136784281716501299369247269452, 6638152083041146951584319435203148,
   1761593450407249393583583129290695244, 1735712938534604872879331524460962380,
   6617473242482727251961402534683212, 7004033637090019381981677963993676,
   1683851451315270527180573478348415564, 440370465541176411775342634438134358604,
   26407509966551881277108258628172, 1767070182873231339710779408320848460,
   1766929149627009649118540948593992268, 6638152107219663343876902929326668,
   6862133840094383941238563898417740, 1725167751508185279116300932686307916,
   103766056445219269197540647500, 1756482367376723250599524148504715852,
   1689043747566924593362560128975135308, 1720238095394250921402661413801714252,
   478358105093721682025466358192925650050497089659468, 1689043747568133519182174758149841484,
   1777170423940552544244643215790858828, 1766968451138078268285735341937943116,
   429700701465099003445587890779783455308, 1720015227502762251104660610018468428,
   1730440465267201723966907090723430988, 1678741078556468701642291108459078220,
   1762000369979458808732594574988173900, 449659486129537245530215703627439039052,
   30082429104731330796709452013426044643861068, 1793052818310812030415995410251014732,
   6800418202390499333777026282447436, 6760560558848489405640426254000716,
   6598144063634286798953936054936140, 1688942730118338486323476162688082508,
   6881307375788178108812932831535692, 1689124880307442853175394380276326988,
   6657964115324422224786567784587852, 6942071979355065738639200117088844,
   1891177002891124601452725149202171657270015582796,
   1937204871906430068082378048094008271281987543628, 117488142996739520683647421840715863056972,
   112722933608119751714091106592393488261708, 492921807971244781941204482258304240362337522704972,
   110711780495687293407849904704141004661324, 7254741569594702408917628105839234476816491084,
   1942847830560950496522357096652528419772560073292,
   8344659456745239518835258836718917140807189619010821710412,
   8344659456745239518835284614709860603657121213526028608076,
   7500048404345703576332065700500020051250537036,
   497380462690904111792755843646049002689302136382028,
   497380462690904111792755825512161708469864515789388,
   7255001537316466809363090935803675184819102284,
   124323009787508435080264278684904258057290668412002892,
   113770364964559026517066036745998382686796, 1874048808645993223150499962753488141663450456652,
   29641767385977996202990753082039742036206156,
   473922331291173888523854110977471469075569146880588,
   7588292450810246046868681136709366371798770252, 450973480609602893741873049618212479564,
   444368757391549029012811359326506345036, 113758401892317647520656445509195856110156,
   29125213430928376599124507351493420535013964,
   495850230334149052562042136312029541746914385224268,
   29647206581480226543416370469193493749981772,
   473922309248707082439257213050142919907538151170636,
   29125213430928220295896363556472793598812748,
   479756495013374265127637497992351113763050947895884, 6821173193186296558891657924993612,
   29906497768037629531705354645919626408256076,
   544297799329924054248500163978062364261933692772940, 121624908234166031500913646392706566218316,
   940217292413193788758609120427639321524088727387568649454246789674521362850243133329124426018243001612508612711220571109788034330813004,
   17740407130094678063673089884256875218968734827569625186374314336698578890403298115853935130792797861338211864301846600551345529398030207050316,
   7043247918906501349609977254987418258284403222913236261584024226074019212951456112950231830002848740549290028943157877623631804657821972679477831310645694259341900954737786685969641133385989025214227046988,
   17740407130094678063673089884256875218968734827569625186374314336698578890403298115853935130792797861338211864301846600579679728295248078332492,
   121428802336216206740958059929080174872702535030001388262469165644,
   723510575035956901380327913738874742029515191727491810128586290066398996996788868375116,
   392357621476765017069117385598760149580, 1720940944893170330395212,
   2337788752526703604478181265127678412558030166387131780194892,
   392357621476764974567819039771953226316, 1720940944883274725745228,
   100443551098051837427701832470203684643404, 440560881899928176862978636,
   25713549081101272253248734774160019719742028, 112783585766826308560082461260,
   521532734826497016649662551218561087122972325775062832838783014564719780428,
   2287522883088336244638867367476247085107051579558290160116300,
   475133828538666563716956634395167187532, 5929460300,
   8305484458331914469687225591893442926933205580, 391900287758433, 364434038743628,
   1725535266710405929263692, 1923124077015793602518953244536627788, 26544582836783702604,
   26833945709912023628, 6870505057665443193420, 6722644552554359054924, 26836467989586141772,
   1758517694672355044647500, 434525774710203846973219404, 114644184857577062080820568652,
   432098475157049142409978444, 1758754755997264037831244, 28477081171407909146983557521996,
   441717865076638021795471948, 532605425241745453507524652420459454565755214651980,
   10040726237058829336038956037158422865491579578865221826606303537816140,
   1720940944893187426378316, 29507634793561199066758578463308,
   32443336247060855527692384442150408768217676, 1720940944883291821728332,
   29507634793561199056862973813324, 440560881899928193958961740,
   7553954507151666968362408892719692, 112783585766826308577178444364,
   1933812353830826744345467600220480076,
   2287522883088336244638867367476247085107051579558307256099404,
   39222374256998602510383582347347576723698573932127104238925854302796, 26551047965155025484,
   21443945562685259940194543208518850716462490460939958132739723711410377081191151440964616275978309693455963273457051434131222889171775000262253085094578444401598292556,
   4130510410781641971243815729521988181738656212745178011287107779531892825192819003144346965421172215062035183656558876492270549099084,
   347258933062786887722310869030994229251303541599800737262844346000669764602069786112031990583902778691737816437351781070456965832906708925424134536603916061232688800568468044,
   14675309732705565074030913594148748258265031306738635961886173605751331772666767873879749774664786415612627280284377676,
   199098756063051462948973938692521731521651768503685755770955283472986575195698672980314793475122103330578163851852,
   315830159763924609908200062846761691851585118060393371986311575226853889520466453359098277542255333139413589918583198419797314321740407678778429249749572985315916,
   18824944482083595389616493156336660539992304479654391158405958599866038147692944645984353606309470615050933319386131119793351767109244874459637186963464780,
   18824944482083595389616493156338746573606368140482687792784104768287650040161115619126368525447178176539785339878838848075687585034228539373981834123436620,
   264647640484959763865389019903819785952308859363168064219495420523764233297173923818509680847163467489330021194853165396005082466155004246208488956492,
   4038202522048336241631241153121702865337799034346799214194363825607522301590310779484975063667576030791988932140490780728847279156662278673949260,
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

def callOrder : List Nat := [
401,402]

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

theorem idem_pattern : U.ax2685.ax.pattern = .equals (srtOf c Srt.set) KoreAML.R (symApp c setConcat [kVar, kVar]) kVar := by
  decide +kernel
theorem idem_trS : (trS U.ax2685).pat = (trAxiom [] [] U.ax2685).pat := by decide +kernel

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
theorem idem_vars : (U.ax2685.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax2685.ax.pattern).eraseDups =
    [.sortVar "R", .evar "K" (KoreAML.srt "Set")] := by decide +kernel
theorem idem_sort : KoreAML.sortOf [] U.ax2685.ax.pattern = some KoreAML.R := by decide +kernel
theorem symApp_withHooks (f : Sym) (ps : List Kore.Pattern) : symApp (cH H) f ps = symApp c f ps := rfl

/-- **Sentence 2685 is refuted, for every H**: Γ with it has no model. At `K = SetItem(0)` the
sentence says `_Set_(K, K)` denotes `K`'s element, and `ΓDomains` (the hook's graph, the two sets
sharing a member) says it denotes nothing. -/
theorem idem_refuted : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax2685).pat) := by
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
  let tbl : KoreAML.VarTable := KoreAML.tableOf U.ax2685.ax.sortVars U.ax2685.ax.pattern
  let val : KoreAML.VarKey → M := fun
    | .sortVar _ => σS
    | _ => a
  let e' : Valuation M := valOf tbl val
  have hRmem : KoreAML.VarKey.sortVar "R" ∈ tbl := by decide +kernel
  have hKmem : KoreAML.VarKey.evar "K" (KoreAML.srt "Set") ∈ tbl := by decide +kernel
  have hRv : ∀ b, (KoreAML.trSort tbl KoreAML.R).interpret I e' b ↔ b = σS := fun b => by
    rw [trSort_R, KoreAML.interp_evar, valOf_ev hRmem]
  have hKv : e'.evalEvar (tbl.ev (.evar "K" (KoreAML.srt "Set"))) = a := valOf_ev hKmem
  have hg : ∀ k ∈ (U.ax2685.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax2685.ax.pattern).eraseDups,
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


/-! ## Library sample: sentence 2837, `I -Int 0 = I` (a `simplification`), at values (Ev) -/

def vI : Kore.Pattern := KoreAML.ev "VarI" (KoreAML.srt "Int")
def kI : VarKey := .evar "VarI" (KoreAML.srt "Int")

theorem s166_trS : (trS U.ax2837).pat = (trAxiom [] [] U.ax2837).pat := by decide +kernel
theorem s166_pattern : U.ax2837.ax.pattern = .implies KoreAML.R (.top KoreAML.R)
    (.equals (KoreAML.srt "Int") KoreAML.R (.app ⟨⟨"Lbl'Unds'-Int'Unds'"⟩⟩ [] [vI, .dv (KoreAML.srt "Int") "0"])
      (.and (KoreAML.srt "Int") [vI, .top (KoreAML.srt "Int")])) := by decide +kernel
theorem s166_free : (U.ax2837.ax.sortVars.map sortVarKey ++ freeOf [] U.ax2837.ax.pattern).eraseDups = [.sortVar "R", kI] := by
  decide +kernel
theorem s166_sortVars : U.ax2837.ax.sortVars = [KoreAML.Rv] := by decide +kernel
theorem sub_name (H : HookParams) : (cH H).symName intSub = "Lbl'Unds'-Int'Unds'" ∧ iteSort? "Lbl'Unds'-Int'Unds'" = none :=
  (by decide +kernel : c.symName intSub = "Lbl'Unds'-Int'Unds'" ∧ iteSort? "Lbl'Unds'-Int'Unds'" = none)
theorem den_int0 (H : HookParams) : den (cH H) (KCore.int 0) = KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt") := by
  show den c (KCore.int 0) = _; decide +kernel
theorem int_numbered (H : HookParams) : Srt.int < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.int < nRegSorts + c.sortNames.length)
theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" := (by decide +kernel : c.sortName Srt.int = "Int")

/-- **Sentence 2837 holds at every value of `I`, in every model of Γ, for every H** (Ev): where `I`
denotes the element of the integer `n`, the translated sentence holds. From `ΓDomains`' graph of
`-Int` at `[n, 0]`, which is `n` for every `n`. -/
theorem lib166 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    (n : Int) (e : Valuation M)
    (he : e.evalEvar ((tableOf U.ax2837.ax.sortVars U.ax2837.ax.pattern).ev kI) = elemOf (cH H) I (KCore.int n)) :
    Valuation.satifies I e (trS U.ax2837).pat := by
  intro m
  rw [s166_trS]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  unfold trAxiom
  dsimp only
  rw [s166_free]
  generalize ht : tableOf U.ax2837.ax.sortVars U.ax2837.ax.pattern = t at he ⊢
  rw [s166_pattern]
  rw [interpret_impl]
  intro hg
  simp only [List.map, conjList, interpret_conj] at hg
  have hR := (interp_guard_sortVar hD).mp hg.1
  have hIg := (interp_guard_evar hD).mp hg.2
  rw [interp_equal hD]
  intro a
  obtain ⟨σI, hσI1, hσI2⟩ := sortSing hI (int_numbered H)
  rw [int_name] at hσI1
  have hS : ∀ b, (trSort t (KoreAML.srt "Int")).interpret I e b ↔ b = σI := fun b => by
    rw [trSort_srt]; exact hσI1 b
  have hRv : ∀ b, (trSort t KoreAML.R).interpret I e b ↔ b = e.evalEvar (t.ev (.sortVar "R")) := fun b => by
    rw [trSort_R, KoreAML.interp_evar]
  obtain ⟨hes, hesort⟩ := elemOf_spec hI (show (cH H).sortOf (KCore.int n) = some Srt.int from rfl) e
  obtain ⟨hes0, -⟩ := elemOf_spec hI (show (cH H).sortOf (KCore.int 0) = some Srt.int from rfl) e
  have hgraph := sat_dom hI (Or.inl ⟨⟨intSub, [Srt.int, Srt.int], Srt.int⟩, [KCore.int n, KCore.int 0], some (KCore.int (n - 0)),
    by decide +kernel, rfl, rfl, fun h => absurd h (by simp), rfl⟩)
  have hg2 := (KoreAML.interp_equal hD).mp (hgraph e default)
  simp only [Int.sub_zero] at hg2
  -- the left side at `e` is the graph's application
  have hL : ∀ b, (tr ⟨t, []⟩ (.app ⟨⟨"Lbl'Unds'-Int'Unds'"⟩⟩ [] [vI, .dv (KoreAML.srt "Int") "0"])).interpret I e b ↔
      (KoreAML.den (symApp (cH H) intSub (GroundTerm.koreList (cH H) [KCore.int n, KCore.int 0]))).interpret I e b := by
    intro b
    have h1 : tr ⟨t, []⟩ (.app ⟨⟨"Lbl'Unds'-Int'Unds'"⟩⟩ [] [vI, .dv (KoreAML.srt "Int") "0"]) =
        (KoreAML.sym (.symbol "Lbl'Unds'-Int'Unds'") ⬝ .evar (t.ev kI)) ⬝ (KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt")) := rfl
    have h2 : KoreAML.den (symApp (cH H) intSub (GroundTerm.koreList (cH H) [KCore.int n, KCore.int 0])) =
        (KoreAML.sym (.symbol "Lbl'Unds'-Int'Unds'") ⬝ den (cH H) (KCore.int n)) ⬝ den (cH H) (KCore.int 0) := by
      unfold symApp; rw [(sub_name H).1, (sub_name H).2]; rfl
    rw [h1, h2]
    refine interp_app_congr (fun m => interp_app_congr (fun _ => Iff.rfl) (fun m => ?_) m) (fun m => ?_) b
    · rw [interp_evar, he, hes]
    · rw [den_int0]
  simp only [sortOf]
  rw [KoreAML.tr, interp_sImp]
  constructor
  · exact fun h => h.1
  · intro ha
    refine ⟨ha, fun _ => ?_⟩
    rw [KoreAML.tr, interp_sEquals hD hc hS hRv hσI2 hR]
    refine ⟨(interp_inhOf_of hRv).mp ha, fun b hb => ?_⟩
    rw [hL b, hg2 b, hes b]
    rw [KoreAML.tr]
    show _ ↔ (sAnd (tr ⟨t, []⟩ vI) (tr ⟨t, []⟩ (.top (KoreAML.srt "Int")))).interpret I e b
    rw [interp_sAnd, KoreAML.tr]
    show _ ↔ (Pattern.evar (t.ev kI)).interpret I e b ∧ (sTop (trSort t (KoreAML.srt "Int"))).interpret I e b
    rw [interp_evar, he, interp_sTop hD (by rw [trSort_srt]; rfl), interp_inhOf_of hS]
    exact ⟨fun h => ⟨h, hb⟩, And.left⟩


theorem shapesOK_c : c.shapesOK = true := by decide +kernel

/-- The one sort named `Int` is the registry's. -/
theorem int_of_name (S : Srt) (h : KoreAML.srt (c.sortName S) = KoreAML.srt "Int") : S = Srt.int := by
  by_cases hS : S < nRegSorts + c.sortNames.length
  · exact (by decide +kernel : ∀ S ∈ List.range (nRegSorts + c.sortNames.length),
      KoreAML.srt (c.sortName S) = KoreAML.srt "Int" → S = Srt.int) S (List.mem_range.mpr hS) h
  · exfalso
    have hlt : ¬ S < nRegSorts := fun h' => hS (Nat.lt_of_lt_of_le h' (Nat.le_add_right _ _))
    have hge : c.sortNames.length ≤ S - nRegSorts :=
      Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact Nat.le_of_not_lt hS)
    have he : c.sortName S = "" := by
      unfold Semantics.sortName
      simp only [hlt, ↓reduceIte]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]; rfl
    rw [he] at h
    exact absurd h (by decide)
/-- **Sentence 2837 is entailed at values** (`EntailsAtValues`, direction Ev), for every H: a
valuation that sends the sentence's one free variable to a value's element sends it to an
integer's, where `lib166` gives the sentence. -/
theorem lib166_at_values (H : HookParams) : EntailsAtValues (cH H) U.ax2837 (trS U.ax2837).pat := by
  intro M _ I hI e hat m
  obtain ⟨v, S, hS, hv, hden⟩ := hat "VarI" (KoreAML.srt "Int") (by decide +kernel)
  have hS' : S = Srt.int := int_of_name S hS
  subst hS'
  obtain ⟨n, rfl⟩ := shape_int shapesOK_c (by rw [← Semantics.sortOf_withHooks _ H noRaw]; exact hv)
  exact lib166 H hI n e (((elemOf_spec hI hv e).1 _).mp hden) m


/-! ## The parameter functional sentences (2645): owed as `ParamsTotal` -/

/-- The parameter symbols no registry hook interprets that the text declares total
(`Definition.totalParams`): the statements take `ParamsTotal c defn.totalParams H`, that `H` gives
each a value of its result sort at every argument list of its argument sorts. -/
theorem total_params : defn.totalParams.map c.symName = ["LblFloat2String'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'Float"] := by decide +kernel

/-- The text's `functional` sentences of those parameters (`isParamFunctional`). -/
noncomputable def paramFunctionalText : List AxiomDecl := [U.ax2645]

/-- The parameter functional sentences are the account's class `parameter functional`, of the
direction `hypothesis`: Γ states a parameter's graph at values from the interpretation (`ΓDomains`),
so it holds the sentence at values exactly where `H` gives the parameter a value at the values of its
argument sorts, which is `ParamsTotal` at that parameter. -/
theorem paramfunctional_account : paramFunctionalText.map (·.index) = classOf "parameter functional" ∧
    paramFunctionalText.all (fun ad => functionalOfNamed ["LblFloat2String'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'Float"] ad.ax) = true := by
  decide +kernel

/-- The sentence is no parameter's functional sentence, or it is of the class
`parameter functional`. -/
noncomputable def paramFunP (ad : AxiomDecl) : Bool :=
  !functionalOfNamed ["LblFloat2String'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'Float"] ad.ax || (classOf "parameter functional").contains ad.index

theorem paramFunE_0 : (((U.all).drop 0).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_40 : (((U.all).drop 40).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_80 : (((U.all).drop 80).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_120 : (((U.all).drop 120).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_160 : (((U.all).drop 160).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_200 : (((U.all).drop 200).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_240 : (((U.all).drop 240).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_280 : (((U.all).drop 280).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_320 : (((U.all).drop 320).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_360 : (((U.all).drop 360).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_400 : (((U.all).drop 400).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_440 : (((U.all).drop 440).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_480 : (((U.all).drop 480).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_520 : (((U.all).drop 520).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_560 : (((U.all).drop 560).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_600 : (((U.all).drop 600).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_640 : (((U.all).drop 640).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_680 : (((U.all).drop 680).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_720 : (((U.all).drop 720).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_760 : (((U.all).drop 760).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_800 : (((U.all).drop 800).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_840 : (((U.all).drop 840).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_880 : (((U.all).drop 880).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_920 : (((U.all).drop 920).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_960 : (((U.all).drop 960).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_1000 : (((U.all).drop 1000).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_1040 : (((U.all).drop 1040).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_1080 : (((U.all).drop 1080).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_1120 : (((U.all).drop 1120).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_1160 : (((U.all).drop 1160).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_1200 : (((U.all).drop 1200).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_1240 : (((U.all).drop 1240).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_1280 : (((U.all).drop 1280).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_1320 : (((U.all).drop 1320).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_1360 : (((U.all).drop 1360).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_1400 : (((U.all).drop 1400).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_1440 : (((U.all).drop 1440).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_1480 : (((U.all).drop 1480).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_1520 : (((U.all).drop 1520).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_1560 : (((U.all).drop 1560).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_1600 : (((U.all).drop 1600).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_1640 : (((U.all).drop 1640).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_1680 : (((U.all).drop 1680).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_1720 : (((U.all).drop 1720).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_1760 : (((U.all).drop 1760).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_1800 : (((U.all).drop 1800).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_1840 : (((U.all).drop 1840).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_1880 : (((U.all).drop 1880).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_1920 : (((U.all).drop 1920).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_1960 : (((U.all).drop 1960).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_2000 : (((U.all).drop 2000).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_2040 : (((U.all).drop 2040).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_2080 : (((U.all).drop 2080).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_2120 : (((U.all).drop 2120).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_2160 : (((U.all).drop 2160).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_2200 : (((U.all).drop 2200).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_2240 : (((U.all).drop 2240).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_2280 : (((U.all).drop 2280).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_2320 : (((U.all).drop 2320).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_2360 : (((U.all).drop 2360).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_2400 : (((U.all).drop 2400).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_2440 : (((U.all).drop 2440).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_2480 : (((U.all).drop 2480).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_2520 : (((U.all).drop 2520).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_2560 : (((U.all).drop 2560).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_2600 : (((U.all).drop 2600).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_2640 : (((U.all).drop 2640).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_2680 : (((U.all).drop 2680).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_2720 : (((U.all).drop 2720).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_2760 : (((U.all).drop 2760).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_2800 : (((U.all).drop 2800).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_2840 : (((U.all).drop 2840).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_2880 : (((U.all).drop 2880).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_2920 : (((U.all).drop 2920).take 40).all paramFunP = true := by decide +kernel
theorem paramFunE_2960 : ((U.all).drop 2960).all paramFunP = true := by decide +kernel

/-- Every `functional` sentence of the user module of a parameter the text declares total
(`total_params`) is of the class `parameter functional`. -/
theorem paramfunctional_heads : userAxioms.all (fun ad => !functionalOfNamed ["LblFloat2String'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'Float"] ad.ax || (classOf "parameter functional").contains ad.index) = true := by
  rw [userAxioms_eq]; exact
    tieAll_whole (l := U.all) (p := paramFunP) <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 0) (n := 40) paramFunE_0 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 40) (n := 40) paramFunE_40 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 80) (n := 40) paramFunE_80 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 120) (n := 40) paramFunE_120 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 160) (n := 40) paramFunE_160 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 200) (n := 40) paramFunE_200 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 240) (n := 40) paramFunE_240 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 280) (n := 40) paramFunE_280 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 320) (n := 40) paramFunE_320 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 360) (n := 40) paramFunE_360 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 400) (n := 40) paramFunE_400 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 440) (n := 40) paramFunE_440 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 480) (n := 40) paramFunE_480 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 520) (n := 40) paramFunE_520 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 560) (n := 40) paramFunE_560 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 600) (n := 40) paramFunE_600 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 640) (n := 40) paramFunE_640 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 680) (n := 40) paramFunE_680 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 720) (n := 40) paramFunE_720 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 760) (n := 40) paramFunE_760 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 800) (n := 40) paramFunE_800 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 840) (n := 40) paramFunE_840 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 880) (n := 40) paramFunE_880 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 920) (n := 40) paramFunE_920 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 960) (n := 40) paramFunE_960 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 1000) (n := 40) paramFunE_1000 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 1040) (n := 40) paramFunE_1040 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 1080) (n := 40) paramFunE_1080 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 1120) (n := 40) paramFunE_1120 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 1160) (n := 40) paramFunE_1160 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 1200) (n := 40) paramFunE_1200 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 1240) (n := 40) paramFunE_1240 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 1280) (n := 40) paramFunE_1280 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 1320) (n := 40) paramFunE_1320 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 1360) (n := 40) paramFunE_1360 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 1400) (n := 40) paramFunE_1400 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 1440) (n := 40) paramFunE_1440 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 1480) (n := 40) paramFunE_1480 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 1520) (n := 40) paramFunE_1520 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 1560) (n := 40) paramFunE_1560 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 1600) (n := 40) paramFunE_1600 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 1640) (n := 40) paramFunE_1640 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 1680) (n := 40) paramFunE_1680 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 1720) (n := 40) paramFunE_1720 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 1760) (n := 40) paramFunE_1760 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 1800) (n := 40) paramFunE_1800 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 1840) (n := 40) paramFunE_1840 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 1880) (n := 40) paramFunE_1880 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 1920) (n := 40) paramFunE_1920 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 1960) (n := 40) paramFunE_1960 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 2000) (n := 40) paramFunE_2000 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 2040) (n := 40) paramFunE_2040 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 2080) (n := 40) paramFunE_2080 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 2120) (n := 40) paramFunE_2120 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 2160) (n := 40) paramFunE_2160 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 2200) (n := 40) paramFunE_2200 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 2240) (n := 40) paramFunE_2240 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 2280) (n := 40) paramFunE_2280 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 2320) (n := 40) paramFunE_2320 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 2360) (n := 40) paramFunE_2360 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 2400) (n := 40) paramFunE_2400 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 2440) (n := 40) paramFunE_2440 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 2480) (n := 40) paramFunE_2480 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 2520) (n := 40) paramFunE_2520 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 2560) (n := 40) paramFunE_2560 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 2600) (n := 40) paramFunE_2600 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 2640) (n := 40) paramFunE_2640 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 2680) (n := 40) paramFunE_2680 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 2720) (n := 40) paramFunE_2720 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 2760) (n := 40) paramFunE_2760 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 2800) (n := 40) paramFunE_2800 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 2840) (n := 40) paramFunE_2840 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 2880) (n := 40) paramFunE_2880 <|
      tieAll_range (l := U.all) (p := paramFunP) (a := 2920) (n := 40) paramFunE_2920 <|
      paramFunE_2960

end KCore.TieE2CellsStream

#check @KCore.TieE2CellsStream.noRaw
#check @KCore.TieE2CellsStream.readsConfined_c
#check @KCore.TieE2CellsStream.userAxioms_eq
#check @KCore.TieE2CellsStream.coreOK
#check @KCore.TieE2CellsStream.wf_defn
#check @KCore.TieE2CellsStream.account
#check @KCore.TieE2CellsStream.account_sizes
#check @KCore.TieE2CellsStream.account_classes
#check @KCore.TieE2CellsStream.lists_in_account
#check @KCore.TieE2CellsStream.consistent
#check @KCore.TieE2CellsStream.idem_refuted
#check @KCore.TieE2CellsStream.lib166
#check @KCore.TieE2CellsStream.lib166_at_values
#check @KCore.TieE2CellsStream.total_params
#check @KCore.TieE2CellsStream.paramfunctional_account
#check @KCore.TieE2CellsStream.paramfunctional_heads
#print axioms KCore.TieE2CellsStream.noRaw
#print axioms KCore.TieE2CellsStream.readsConfined_c
#print axioms KCore.TieE2CellsStream.userAxioms_eq
#print axioms KCore.TieE2CellsStream.coreOK
#print axioms KCore.TieE2CellsStream.wf_defn
#print axioms KCore.TieE2CellsStream.account
#print axioms KCore.TieE2CellsStream.account_sizes
#print axioms KCore.TieE2CellsStream.account_classes
#print axioms KCore.TieE2CellsStream.lists_in_account
#print axioms KCore.TieE2CellsStream.consistent
#print axioms KCore.TieE2CellsStream.idem_refuted
#print axioms KCore.TieE2CellsStream.lib166
#print axioms KCore.TieE2CellsStream.lib166_at_values
#print axioms KCore.TieE2CellsStream.total_params
#print axioms KCore.TieE2CellsStream.paramfunctional_account
#print axioms KCore.TieE2CellsStream.paramfunctional_heads
